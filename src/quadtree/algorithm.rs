use super::{
    LEAF_SIZE, LEAF_SIZE_LOG2,
    blank::BlankNodes,
    hashtable::{Idx, NodeAccess},
    sharded_statistics::{MetricKind, record_metric},
    spin::Spinner,
    status,
};
use std::sync::atomic::Ordering;

/// Apply Conway's Game of Life rules to a row of cells.
///
/// Uses bit-parallel computation to update 16 cells simultaneously.
/// Implements the standard B3/S23 rule.
fn update_row(row_prev: u16, row_curr: u16, row_next: u16) -> u16 {
    let b = row_prev;
    let a = b << 1;
    let c = b >> 1;
    let i = row_curr;
    let h = i << 1;
    let d = i >> 1;
    let f = row_next;
    let g = f << 1;
    let e = f >> 1;

    let ab0 = a ^ b;
    let ab1 = a & b;
    let cd0 = c ^ d;
    let cd1 = c & d;

    let ef0 = e ^ f;
    let ef1 = e & f;
    let gh0 = g ^ h;
    let gh1 = g & h;

    let ad0 = ab0 ^ cd0;
    let ad1 = (ab1 ^ cd1) ^ (ab0 & cd0);
    let ad2 = ab1 & cd1;

    let eh0 = ef0 ^ gh0;
    let eh1 = (ef1 ^ gh1) ^ (ef0 & gh0);
    let eh2 = ef1 & gh1;

    let ah0 = ad0 ^ eh0;
    let xx = ad0 & eh0;
    let yy = ad1 ^ eh1;
    let ah1 = xx ^ yy;
    let ah23 = (ad2 | eh2) | (ad1 & eh1) | (xx & yy);
    let z = !ah23 & ah1;
    let i2 = !ah0 & z;
    let i3 = ah0 & z;
    (i & i2) | i3
}

/// Update a 2x2 block of leaf nodes by simulating `steps` generations.
///
/// This is the base case of Hashlife recursion. Combines 4 leaf nodes (8x8 each)
/// into a 16x16 grid, simulates forward, and extracts the center 8x8 result.
/// `nw`, `ne`, `sw`, `se` must be leaves.
pub(super) fn update_leaves<Meta: Default + Sync>(
    mem: &impl NodeAccess<Meta>,
    nw: Idx,
    ne: Idx,
    sw: Idx,
    se: Idx,
    steps: u64,
) -> Idx {
    let [nw, ne, sw, se] = [nw, ne, sw, se].map(|x| mem.get(x).leaf_cells());

    let mut src = [0; 16];
    for i in 0..8 {
        src[i] = u16::from_le_bytes([nw[i], ne[i]]);
        src[i + 8] = u16::from_le_bytes([sw[i], se[i]]);
    }
    let mut dst = [0; 16];

    for t in 1..=steps as usize {
        for y in t..16 - t {
            dst[y] = update_row(src[y - 1], src[y], src[y + 1]);
        }
        std::mem::swap(&mut src, &mut dst);
    }

    let arr: [u16; 8] = src[4..12].try_into().unwrap();
    mem.find_or_create_leaf_from_u64(u64::from_le_bytes(arr.map(|x| (x >> 4) as u8)))
}

/// Create 9 overlapping children from a 2x2 block of nodes.
///
/// ```text
/// Input: 2×2 block         Output: 9 overlapping children
/// ┌─────┬─────┐            ┌─────┬─────┬─────┐
/// │ NW  │ NE  │            │  0  │  1  │  2  │
/// │     │     │            │(NW) │(mid)│(NE) │
/// ├─────┼─────┤            ├─────┼─────┼─────┤
/// │ SW  │ SE  │            │  3  │  4  │  5  │
/// │     │     │            │(mid)│(ctr)│(mid)│
/// └─────┴─────┘            ├─────┼─────┼─────┤
///                          │  6  │  7  │  8  │
///                          │(SW) │(mid)│(SE) │
///                          └─────┴─────┴─────┘
///
/// Children 0,2,6,8 are the original input nodes.
/// Children 1,3,5,7 are formed from overlapping edges.
/// Child 4 is formed from the center where all four inputs meet.
/// ```
pub(super) fn nine_children_overlapping<Meta: Default + Sync>(
    mem: &impl NodeAccess<Meta>,
    nw: Idx,
    ne: Idx,
    sw: Idx,
    se: Idx,
) -> [Idx; 9] {
    let [nw_, ne_, sw_, se_] = [nw, ne, sw, se].map(|x| mem.get(x));
    [
        nw,
        mem.find_or_create_node(nw_.ne, ne_.nw, nw_.se, ne_.sw),
        ne,
        mem.find_or_create_node(nw_.sw, nw_.se, sw_.nw, sw_.ne),
        mem.find_or_create_node(nw_.se, ne_.sw, sw_.ne, se_.nw),
        mem.find_or_create_node(ne_.sw, ne_.se, se_.nw, se_.ne),
        sw,
        mem.find_or_create_node(sw_.ne, se_.nw, sw_.se, se_.sw),
        se,
    ]
}

/// Create 9 non-overlapping children from a 2x2 block of nodes.
///
/// ```text
/// Input: 2×2 block          Each input node has 4 children:
/// ┌──────┬──────┐           ┌───┬───┐
/// │  NW  │  NE  │           │nw │ne │
/// │      │      │           ├───┼───┤
/// ├──────┼──────┤           │sw │se │
/// │  SW  │  SE  │           └───┴───┘
/// │      │      │
/// └──────┴──────┘
///
/// Output: 9 non-overlapping children formed from centers:
/// ┌─────┬─────┬─────┐
/// │  0  │  1  │  2  │  ← 0: from NW's children, 1: from NW+NE, 2: from NE's children
/// ├─────┼─────┼─────┤
/// │  3  │  4  │  5  │  ← 3: from NW+SW, 4: from all four, 5: from NE+SE
/// ├─────┼─────┼─────┤
/// │  6  │  7  │  8  │  ← 6: from SW's children, 7: from SW+SE, 8: from SE's children
/// └─────┴─────┴─────┘
///
/// Each output is formed by taking center regions from the input nodes' children.
/// ```
pub(super) fn nine_children_disjoint<Meta: Default + Sync>(
    mem: &impl NodeAccess<Meta>,
    nw: Idx,
    ne: Idx,
    sw: Idx,
    se: Idx,
    size_log2: u32,
) -> [Idx; 9] {
    let [
        [nwnw, nwne, nwsw, nwse],
        [nenw, nene, nesw, nese],
        [swnw, swne, swsw, swse],
        [senw, sene, sesw, sese],
    ] = [nw, ne, sw, se].map(|x| mem.get(x).parts().map(|y| mem.get(y)));

    [
        [nwnw, nwne, nwsw, nwse],
        [nwne, nenw, nwse, nesw],
        [nenw, nene, nesw, nese],
        [nwsw, nwse, swnw, swne],
        [nwse, nesw, swne, senw],
        [nesw, nese, senw, sene],
        [swnw, swne, swsw, swse],
        [swne, senw, swse, sesw],
        [senw, sene, sesw, sese],
    ]
    .map(|[nw, ne, sw, se]| {
        if size_log2 >= LEAF_SIZE_LOG2 + 2 {
            mem.find_or_create_node(nw.se, ne.sw, sw.ne, se.nw)
        } else {
            mem.find_or_create_leaf_from_parts(
                nw.leaf_se(),
                ne.leaf_sw(),
                sw.leaf_ne(),
                se.leaf_nw(),
            )
        }
    })
}

/// Combine 9 overlapping children into 4 final children.
///
/// ```text
/// Input:           Output:
/// ┌───┬───┬───┐    ┌─────┬─────┐
/// │ 0 │ 1 │ 2 │    │  A  │  B  │
/// ├───┼───┼───┤    │     │     │
/// │ 3 │ 4 │ 5 │    ├─────┼─────┤
/// ├───┼───┼───┤    │  C  │  D  │
/// │ 6 │ 7 │ 8 │    │     │     │
/// └───┴───┴───┘    └─────┴─────┘
///
/// A = combine(0,1,3,4)
/// B = combine(1,2,4,5)
/// C = combine(3,4,6,7)
/// D = combine(4,5,7,8)
/// ```
pub(super) fn four_children_overlapping<Meta: Default + Sync>(
    mem: &impl NodeAccess<Meta>,
    arr: &[Idx; 9],
) -> [Idx; 4] {
    [
        mem.find_or_create_node(arr[0], arr[1], arr[3], arr[4]),
        mem.find_or_create_node(arr[1], arr[2], arr[4], arr[5]),
        mem.find_or_create_node(arr[3], arr[4], arr[6], arr[7]),
        mem.find_or_create_node(arr[4], arr[5], arr[7], arr[8]),
    ]
}

fn determine_direction<Meta: Default + Sync>(
    mem: &impl NodeAccess<Meta>,
    nw: Idx,
    ne: Idx,
    sw: Idx,
    se: Idx,
) -> u64 {
    let m = update_leaves(mem, nw, ne, sw, se, 4);
    let centre = u64::from_le_bytes(mem.get(m).leaf_cells());

    let [nw, ne, sw, se] = [nw, ne, sw, se].map(|x| u64::from_le_bytes(mem.get(x).leaf_cells()));

    let z64_centre_to_u64 = |x, y| {
        let xs = (4 + x) as u64;
        let ys = ((4 + y) << 3) as u64;
        let bitmask = (0x0101010101010101 << xs) - 0x0101010101010101;
        let left = (nw >> ys) | (sw << (64 - ys));
        let right = (ne >> ys) | (se << (64 - ys));
        ((right & bitmask) << (8 - xs)) | ((left & (!bitmask)) >> xs)
    };

    let mut dmap = 0;
    if centre == z64_centre_to_u64(-1, -1) {
        dmap |= 1
    } // SE
    if centre == z64_centre_to_u64(0, -2) {
        dmap |= 2
    } // S
    if centre == z64_centre_to_u64(1, -1) {
        dmap |= 4
    } // SW
    if centre == z64_centre_to_u64(2, 0) {
        dmap |= 8
    } // W
    if centre == z64_centre_to_u64(1, 1) {
        dmap |= 16
    } // NW
    if centre == z64_centre_to_u64(0, 2) {
        dmap |= 32
    } // N
    if centre == z64_centre_to_u64(-1, 1) {
        dmap |= 64
    } // NE
    if centre == z64_centre_to_u64(-2, 0) {
        dmap |= 128
    } // E

    let mut lmask = 0;
    if centre != 0 {
        if dmap & 170 != 0 {
            lmask |= 3;
        }
        if dmap & 85 != 0 {
            lmask |= 7;
        }
    }

    // Use a uint64 as an ordered pair of uint32s:
    dmap | (lmask << 32)
}

/// Compute lane descriptors for a node. Thread-safe (uses CAS on `status_extra`).
fn node2lanes(
    mem: &impl NodeAccess<u64>,
    blank_nodes: &BlankNodes,
    idx: Idx,
    size_log2: u32,
) -> u64 {
    if idx == blank_nodes.get(size_log2) {
        // blank node
        return 0xffff;
    }

    let n = mem.get(idx);
    let status = n.status_extra.load(Ordering::Acquire);
    if status == status::FINISHED {
        return unsafe { *n.extra.get() };
    }

    if !(status == status::NOT_STARTED
        && n.status_extra
            .compare_exchange(
                status::NOT_STARTED,
                status::PROCESSING,
                Ordering::Relaxed,
                Ordering::Relaxed,
            )
            .is_ok())
    {
        let mut spinner = Spinner::new();
        while n.status_extra.load(Ordering::Acquire) != status::FINISHED {
            spinner.spin();
        }
        record_metric(spinner.count(), MetricKind::Node2Lanes);
        return unsafe { *n.extra.get() };
    }

    if size_log2 == LEAF_SIZE_LOG2 + 1 {
        let extra = determine_direction(mem, n.nw, n.ne, n.sw, n.se);
        unsafe { *n.extra.get() = extra };
        n.status_extra.store(status::FINISHED, Ordering::Release);
        return extra;
    }

    let (nw, ne, sw, se) = {
        let n = mem.get(idx);
        (n.nw, n.ne, n.sw, n.se)
    };

    let mut childlanes = [0u64; 9];
    let mut adml = 0xff;
    /*
     * Short-circuit evaluation using the corner children
     * This will handle the vast majority of random tiles.
     */
    if adml != 0 {
        childlanes[0] = node2lanes(mem, blank_nodes, nw, size_log2 - 1);
        adml &= childlanes[0];
    }
    if adml != 0 {
        childlanes[2] = node2lanes(mem, blank_nodes, ne, size_log2 - 1);
        adml &= childlanes[2];
    }
    if adml != 0 {
        childlanes[6] = node2lanes(mem, blank_nodes, sw, size_log2 - 1);
        adml &= childlanes[6];
    }
    if adml != 0 {
        childlanes[8] = node2lanes(mem, blank_nodes, se, size_log2 - 1);
        adml &= childlanes[8];
    }
    if adml == 0 {
        unsafe { *n.extra.get() = 0 };
        n.status_extra.store(status::FINISHED, Ordering::Release);
        return 0;
    }

    if size_log2 == LEAF_SIZE_LOG2 + 2 {
        let tlx = {
            let nw = mem.get(nw);
            [nw.nw, nw.ne, nw.sw, nw.se].map(|x| u64::from_le_bytes(mem.get(x).leaf_cells()))
        };
        let trx = {
            let ne = mem.get(ne);
            [ne.nw, ne.ne, ne.sw, ne.se].map(|x| u64::from_le_bytes(mem.get(x).leaf_cells()))
        };
        let blx = {
            let sw = mem.get(sw);
            [sw.nw, sw.ne, sw.sw, sw.se].map(|x| u64::from_le_bytes(mem.get(x).leaf_cells()))
        };
        let brx = {
            let se = mem.get(se);
            [se.nw, se.ne, se.sw, se.se].map(|x| u64::from_le_bytes(mem.get(x).leaf_cells()))
        };

        let cc = [tlx[3], trx[2], blx[1], brx[0]];
        let tc = [tlx[1], trx[0], tlx[3], trx[2]];
        let bc = [blx[1], brx[0], blx[3], brx[2]];
        let cl = [tlx[2], tlx[3], blx[0], blx[1]];
        let cr = [trx[2], trx[3], brx[0], brx[1]];

        let prepared = |x: &[u64; 4]| {
            let nw = mem.find_or_create_leaf_from_u64(x[0]);
            let ne = mem.find_or_create_leaf_from_u64(x[1]);
            let sw = mem.find_or_create_leaf_from_u64(x[2]);
            let se = mem.find_or_create_leaf_from_u64(x[3]);
            mem.find_or_create_node(nw, ne, sw, se)
        };

        for (i, x) in [(1, &tc), (3, &cl), (4, &cc), (5, &cr), (7, &bc)] {
            childlanes[i] = node2lanes(mem, blank_nodes, prepared(x), size_log2 - 1);
        }
        adml &= childlanes[1] & childlanes[3] & childlanes[4] & childlanes[5] & childlanes[7];
    } else {
        let pptr_tl = mem.get(nw);
        let pptr_tr = mem.get(ne);
        let pptr_bl = mem.get(sw);
        let pptr_br = mem.get(se);
        let cc = [pptr_tl.se, pptr_tr.sw, pptr_bl.ne, pptr_br.nw];
        let tc = [pptr_tl.ne, pptr_tr.nw, pptr_tl.se, pptr_tr.sw];
        let bc = [pptr_bl.ne, pptr_br.nw, pptr_bl.se, pptr_br.sw];
        let cl = [pptr_tl.sw, pptr_tl.se, pptr_bl.nw, pptr_bl.ne];
        let cr = [pptr_tr.sw, pptr_tr.se, pptr_br.nw, pptr_br.ne];

        let prepared = |x: &[Idx; 4]| mem.find_or_create_node(x[0], x[1], x[2], x[3]);

        for (i, x) in [(1, &tc), (3, &cl), (4, &cc), (5, &cr), (7, &bc)] {
            childlanes[i] = node2lanes(mem, blank_nodes, prepared(x), size_log2 - 1);
        }
        adml &= childlanes[1] & childlanes[3] & childlanes[4] & childlanes[5] & childlanes[7];
    }
    for x in &mut childlanes {
        *x >>= 32;
    }
    let mut lanes = 0;

    let rotr32 = |x, y| (x >> y) | (x << (32 - y));
    let rotl32 = |x, y| (x << y) | (x >> (32 - y));

    /*
     * Lane numbers are modulo 32, with each lane being either
     * 8 rows, 8 columns, or 8hd (in either diagonal direction)
     */
    let a: u64 = if size_log2 - LEAF_SIZE_LOG2 - 2 <= 4 {
        1 << (size_log2 - LEAF_SIZE_LOG2 - 2)
    } else {
        0
    };
    let a2 = (2 * a) & 31;

    if adml & 0x88 != 0 {
        // Horizontal lanes
        lanes |= rotl32(childlanes[0] | childlanes[1] | childlanes[2], a);
        lanes |= childlanes[3] | childlanes[4] | childlanes[5];
        lanes |= rotr32(childlanes[6] | childlanes[7] | childlanes[8], a);
    }

    if adml & 0x44 != 0 {
        lanes |= rotl32(childlanes[0], a2);
        lanes |= rotl32(childlanes[3] | childlanes[1], a);
        lanes |= childlanes[6] | childlanes[4] | childlanes[2];
        lanes |= rotr32(childlanes[7] | childlanes[5], a);
        lanes |= rotr32(childlanes[8], a2);
    }

    if adml & 0x22 != 0 {
        // Vertical lanes
        lanes |= rotl32(childlanes[0] | childlanes[3] | childlanes[6], a);
        lanes |= childlanes[1] | childlanes[4] | childlanes[7];
        lanes |= rotr32(childlanes[2] | childlanes[5] | childlanes[8], a);
    }

    if adml & 0x11 != 0 {
        lanes |= rotl32(childlanes[2], a2);
        lanes |= rotl32(childlanes[1] | childlanes[5], a);
        lanes |= childlanes[0] | childlanes[4] | childlanes[8];
        lanes |= rotr32(childlanes[3] | childlanes[7], a);
        lanes |= rotr32(childlanes[6], a2);
    }

    let extra = adml | (lanes << 32);
    unsafe { *n.extra.get() = extra };
    n.status_extra.store(status::FINISHED, Ordering::Release);
    extra
}

/// Check if two universes are provably non-interacting (solitonic).
/// Thread-safe.
pub(super) fn is_solitonic(
    mem: &impl NodeAccess<u64>,
    blank_nodes: &BlankNodes,
    idx: (Idx, Idx),
    size_log2: u32,
) -> bool {
    let lanes1 = node2lanes(mem, blank_nodes, idx.0, size_log2);
    if lanes1 & 255 == 0 {
        return false;
    }
    let lanes2 = node2lanes(mem, blank_nodes, idx.1, size_log2);
    if lanes2 & 255 == 0 {
        return false;
    }
    let commonlanes = (lanes1 & lanes2) >> 32;
    if commonlanes != 0 {
        return false;
    }
    (((lanes1 >> 4) & lanes2) | ((lanes2 >> 4) & lanes1)) & 15 != 0
}

/// Compute solitonic case: two non-interacting universes updated independently.
/// Used by the parallel executor for the fast-path.
pub(super) fn compute_solitonic(
    mem: &impl NodeAccess<u64>,
    blank_nodes: &BlankNodes,
    gens_log2: u32,
    idx: (Idx, Idx),
    size_log2: u32,
) -> (Idx, Idx) {
    let i1 = update_node_sync(mem, gens_log2, idx.0, size_log2);
    let i2 = update_node_sync(mem, gens_log2, idx.1, size_log2);

    let b = blank_nodes.get(size_log2);
    if idx.0 == b || idx.1 == b {
        let (i3, ind3) = if idx.0 == b { (i2, idx.1) } else { (i1, idx.0) };
        let lanes = node2lanes(mem, blank_nodes, ind3, size_log2);
        let b = blank_nodes.get(size_log2 - 1);
        if lanes & 0xf0 != 0 { (b, i3) } else { (i3, b) }
    } else {
        (i1, i2)
    }
}

/// Compute base case: merge universes and run standard HashLife.
/// Used by the parallel executor for the smallest recursive level.
pub(super) fn compute_base_case(
    mem: &impl NodeAccess<u64>,
    blank_nodes: &BlankNodes,
    gens_log2: u32,
    idx: (Idx, Idx),
    size_log2: u32,
) -> (Idx, Idx) {
    let hnode2 = merge_universes(mem, blank_nodes, idx, size_log2);
    let i3 = update_node_sync(mem, gens_log2, hnode2, size_log2);
    let b = blank_nodes.get(size_log2 - 1);

    if i3 != b {
        let lanes = node2lanes(mem, blank_nodes, hnode2, size_log2);
        if lanes & 0xf0 != 0 { (b, i3) } else { (i3, b) }
    } else {
        (b, b)
    }
}

fn update_inner_sync(mem: &impl NodeAccess<u64>, gens_log2: u32, node: Idx, size_log2: u32) -> Idx {
    let n = mem.get(node);
    let both_stages = gens_log2 + 2 >= size_log2;
    if size_log2 == LEAF_SIZE_LOG2 + 1 {
        let steps = if both_stages {
            LEAF_SIZE / 2
        } else {
            1 << gens_log2
        };
        update_leaves(mem, n.nw, n.ne, n.sw, n.se, steps)
    } else {
        let mut arr9;
        if both_stages {
            arr9 = nine_children_overlapping(mem, n.nw, n.ne, n.sw, n.se);
            for x in arr9.iter_mut() {
                *x = update_node_sync(mem, gens_log2, *x, size_log2 - 1);
            }
        } else {
            arr9 = nine_children_disjoint(mem, n.nw, n.ne, n.sw, n.se, size_log2 - 1);
        }

        let mut arr4 = four_children_overlapping(mem, &arr9);
        for x in arr4.iter_mut() {
            *x = update_node_sync(mem, gens_log2, *x, size_log2 - 1);
        }

        mem.find_or_create_node(arr4[0], arr4[1], arr4[2], arr4[3])
    }
}

pub(super) fn update_node_sync(
    mem: &impl NodeAccess<u64>,
    gens_log2: u32,
    node: Idx,
    size_log2: u32,
) -> Idx {
    let n = mem.get(node);
    let status = n.status.load(Ordering::Acquire);
    if status == status::FINISHED {
        return n.cache.get_value();
    }

    if status == status::NOT_STARTED
        && n.status
            .compare_exchange(
                status::NOT_STARTED,
                status::PROCESSING,
                Ordering::Relaxed,
                Ordering::Relaxed,
            )
            .is_ok()
    {
        let cache = update_inner_sync(mem, gens_log2, node, size_log2);
        n.cache.set_value(cache);
        n.status.store(status::FINISHED, Ordering::Release);
        cache
    } else {
        let mut spinner = Spinner::new();
        while n.status.load(Ordering::Acquire) != status::FINISHED {
            // if ExecutionStatistics::is_poisoned() {
            //     return Idx::default();
            // }
            spinner.spin();
        }
        record_metric(spinner.count(), MetricKind::UpdateNodeSync);
        n.cache.get_value()
    }
}

/// Merge two non-overlapping universes into a single node. Thread-safe.
pub(super) fn merge_universes(
    mem: &impl NodeAccess<u64>,
    blank_nodes: &BlankNodes,
    idx: (Idx, Idx),
    size_log2: u32,
) -> Idx {
    let b = blank_nodes.get(size_log2);
    if idx.1 == b {
        return idx.0;
    }
    if idx.0 == b {
        return idx.1;
    }
    let m0 = mem.get(idx.0);
    let m1 = mem.get(idx.1);
    if size_log2 == LEAF_SIZE_LOG2 {
        let l0 = u64::from_le_bytes(m0.leaf_cells());
        let l1 = u64::from_le_bytes(m1.leaf_cells());
        assert!(l0 & l1 == 0, "universes overlap");
        mem.find_or_create_leaf_from_u64(l0 | l1)
    } else {
        let (m0, m1) = (m0.parts(), m1.parts());
        let mut r = [Idx::default(); 4];
        for i in 0..4 {
            r[i] = merge_universes(mem, blank_nodes, (m0[i], m1[i]), size_log2 - 1);
        }
        mem.find_or_create_node(r[0], r[1], r[2], r[3])
    }
}
