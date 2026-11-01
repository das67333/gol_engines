use super::{
    LEAF_SIZE_LOG2,
    blank::BlankNodes,
    hashtable::{Idx, NodeAccess, NodeStore},
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

/// Compute the lane descriptor for a node at level `LEAF_SIZE_LOG2 + 1`
/// (a 2×2 block of 8×8 leaves, i.e. a 16×16 grid).
///
/// Returns a `u64` with the encoding used by [`node2lanes`]:
/// - bits 0–7: `adml` (admissible-lane mask) — which lane types are present.
/// - bits 32–63: `lanes` — active lane numbers mod 32.
///
/// The direction map `dmap` checks whether the center 8×8 result (simulated 4
/// steps forward) matches the center pattern shifted by ±1 or ±2 cells in each
/// of the 8 compass directions. Each matching shift sets a bit in `dmap`.
/// `lmask` then encodes which lane types those directions belong to.
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
        let bitmask = (0x0101_0101_0101_0101 << xs) - 0x0101_0101_0101_0101;
        let left = (nw >> ys) | (sw << (64 - ys));
        let right = (ne >> ys) | (se << (64 - ys));
        ((right & bitmask) << (8 - xs)) | ((left & (!bitmask)) >> xs)
    };

    let mut dmap = 0;
    if centre == z64_centre_to_u64(-1, -1) {
        dmap |= 1;
    } // SE
    if centre == z64_centre_to_u64(0, -2) {
        dmap |= 2;
    } // S
    if centre == z64_centre_to_u64(1, -1) {
        dmap |= 4;
    } // SW
    if centre == z64_centre_to_u64(2, 0) {
        dmap |= 8;
    } // W
    if centre == z64_centre_to_u64(1, 1) {
        dmap |= 16;
    } // NW
    if centre == z64_centre_to_u64(0, 2) {
        dmap |= 32;
    } // N
    if centre == z64_centre_to_u64(-1, 1) {
        dmap |= 64;
    } // NE
    if centre == z64_centre_to_u64(-2, 0) {
        dmap |= 128;
    } // E

    let mut lmask = 0;
    if centre != 0 {
        if dmap & 0b1010_1010 != 0 {
            lmask |= 3;
        }
        if dmap & 0b0101_0101 != 0 {
            lmask |= 7;
        }
    }

    // Use a uint64 as an ordered pair of uint32s:
    dmap | (lmask << 32)
}

/// Compute lane descriptors for a node. Thread-safe (uses CAS on `status_extra`).
///
/// Kept synchronous: `node2lanes` is idempotent and cheap to spin on (it only
/// needs the already-present cell data, not async `HashLife` results), so a
/// simple CAS + spinner avoids the cost of adding a `BiTask` phase for it.
/// Called from both `is_solitonic` (the solitonic check inside the binode
/// phase machine) and from the finalization steps of Phases Solitonic / Base.
pub(super) fn node2lanes(
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
    if lanes1.trailing_zeros() >= 8 {
        return false;
    }
    let lanes2 = node2lanes(mem, blank_nodes, idx.1, size_log2);
    if lanes2.trailing_zeros() >= 8 {
        return false;
    }
    let commonlanes = (lanes1 & lanes2) >> 32;
    if commonlanes != 0 {
        return false;
    }
    (((lanes1 >> 4) & lanes2) | ((lanes2 >> 4) & lanes1)) & 15 != 0
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

/// Merge the final roots with a call-local cache of repeated non-leaf pairs.
/// The executor's 32x32 base merge keeps using `merge_universes` unchanged.
/// Returns `None` if an allocating step reaches the store's cancellation limit.
pub(super) fn merge_final_universes(
    mem: &NodeStore<u64>,
    blank_nodes: &BlankNodes,
    idx: (Idx, Idx),
    size_log2: u32,
) -> Option<Idx> {
    let blank = blank_nodes.get(size_log2);
    let mut cache = Vec::new();
    if size_log2 > LEAF_SIZE_LOG2 && idx.0 != blank && idx.1 != blank {
        // At height h there are at most (4^h - 1) / 3 non-leaf pairs to visit.
        let max_log2 = FINAL_MERGE_CACHE_ENTRIES.ilog2();
        let height = (size_log2 - LEAF_SIZE_LOG2).min(max_log2);
        let entries = 1usize << (2 * height - 1).min(max_log2);
        if cache.try_reserve_exact(entries).is_ok() {
            cache.resize(entries, MergeCacheEntry::default());
        }
    }
    FinalMerge {
        mem,
        blank_nodes,
        cache,
        hasher: ahash::RandomState::new(),
    }
    .merge(idx, size_log2)
}

const FINAL_MERGE_CACHE_BYTES: usize = 4 << 20;
const FINAL_MERGE_CACHE_ENTRIES: usize =
    1usize << (FINAL_MERGE_CACHE_BYTES / std::mem::size_of::<MergeCacheEntry>()).ilog2();

#[derive(Clone, Copy, Default)]
struct MergeCacheEntry {
    key: u64,
    result: Idx,
}

struct FinalMerge<'a> {
    mem: &'a NodeStore<u64>,
    blank_nodes: &'a BlankNodes,
    cache: Vec<MergeCacheEntry>,
    hasher: ahash::RandomState,
}

impl FinalMerge<'_> {
    fn merge(&mut self, idx: (Idx, Idx), size_log2: u32) -> Option<Idx> {
        let blank = self.blank_nodes.get(size_log2);
        if idx.1 == blank {
            return Some(idx.0);
        }
        if idx.0 == blank {
            return Some(idx.1);
        }
        if size_log2 <= LEAF_SIZE_LOG2 {
            return (!self.mem.exceeds_load_factor())
                .then(|| merge_universes(self.mem, self.blank_nodes, idx, size_log2));
        }
        // Live node IDs are nonzero; zero tags mark unused slots. IDs stay valid for this call.
        let key = (u64::from(idx.0) << 32) | u64::from(idx.1);
        let slot = (!self.cache.is_empty()).then(|| self.hasher.hash_one(key) as usize & (self.cache.len() - 1));
        if let Some(slot) = slot
            && self.cache[slot].key == key
        {
            return Some(self.cache[slot].result);
        }
        let (a, b) = (self.mem.get(idx.0).parts(), self.mem.get(idx.1).parts());
        let mut parts = [Idx::default(); 4];
        for i in 0..4 {
            parts[i] = self.merge((a[i], b[i]), size_log2 - 1)?;
        }
        if self.mem.exceeds_load_factor() {
            return None;
        }
        let result = self
            .mem
            .find_or_create_node(parts[0], parts[1], parts[2], parts[3]);
        // Children may replace this slot; publish only the fully computed pair.
        if let Some(slot) = slot {
            self.cache[slot] = MergeCacheEntry { key, result };
        }
        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quadtree::hashtable::NodeStore;

    #[test]
    fn final_merge_preserves_shared_subtrees_and_empty_roots() {
        let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
        let mut blanks = BlankNodes::new();
        let size_log2 = LEAF_SIZE_LOG2 + 8;
        let blank = blanks.get_mut(size_log2, &mem);
        let mut a = mem.find_or_create_leaf_from_u64(0x0000_0000_0000_000f);
        let mut b = mem.find_or_create_leaf_from_u64(0x0000_0000_f000_0000);
        let mut expected = mem.find_or_create_leaf_from_u64(0x0000_0000_f000_000f);
        for _ in LEAF_SIZE_LOG2..size_log2 {
            a = mem.find_or_create_node(a, a, a, a);
            b = mem.find_or_create_node(b, b, b, b);
            expected = mem.find_or_create_node(expected, expected, expected, expected);
        }
        assert_eq!(merge_universes(&mem, &blanks, (a, b), size_log2), expected);
        assert_eq!(
            merge_final_universes(&mem, &blanks, (a, b), size_log2),
            Some(expected)
        );
        assert_eq!(
            merge_final_universes(&mem, &blanks, (b, a), size_log2),
            Some(expected)
        );
        assert_eq!(
            merge_final_universes(&mem, &blanks, (a, blank), size_log2),
            Some(a)
        );
        assert_eq!(
            merge_final_universes(&mem, &blanks, (blank, b), size_log2),
            Some(b)
        );
    }

    #[test]
    fn final_merge_cache_stays_within_memory_budget() {
        let entry_bytes = std::mem::size_of::<MergeCacheEntry>();
        assert!(FINAL_MERGE_CACHE_ENTRIES.is_power_of_two());
        assert!(FINAL_MERGE_CACHE_ENTRIES * entry_bytes <= FINAL_MERGE_CACHE_BYTES);
        #[cfg(target_pointer_width = "64")]
        assert_eq!(entry_bytes, 16);
    }

    fn one_slot_merge<'a>(
        mem: &'a NodeStore<u64>,
        blank_nodes: &'a BlankNodes,
    ) -> FinalMerge<'a> {
        FinalMerge {
            mem,
            blank_nodes,
            cache: vec![MergeCacheEntry::default()],
            hasher: ahash::RandomState::new(),
        }
    }

    #[test]
    fn final_merge_stops_when_a_child_exhausts_capacity() {
        // Discover the public cancellation boundary without pinning sharding constants.
        let probe = NodeStore::<u64>::new(10, 1 << 10, 1);
        for cells in 0.. {
            if probe.exceeds_load_factor() {
                break;
            }
            probe.find_or_create_leaf_from_u64((1 << 63) | cells);
        }
        let last_available = probe.len() - 1;

        // An empty cache is also the fallback when its allocation fails.
        for cache_entries in [0, 1] {
            let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
            let mut blanks = BlankNodes::new();
            let size_log2 = LEAF_SIZE_LOG2 + 2;
            blanks.get_mut(size_log2, &mem);
            let mut a = mem.find_or_create_leaf_from_u64(1);
            let mut b = mem.find_or_create_leaf_from_u64(2);
            for _ in LEAF_SIZE_LOG2..size_log2 {
                a = mem.find_or_create_node(a, a, a, a);
                b = mem.find_or_create_node(b, b, b, b);
            }
            for cells in 0.. {
                if mem.len() == last_available {
                    break;
                }
                mem.find_or_create_leaf_from_u64((1 << 63) | cells);
            }
            assert!(!mem.exceeds_load_factor());
            let mut merge = FinalMerge {
                mem: &mem,
                blank_nodes: &blanks,
                cache: vec![MergeCacheEntry::default(); cache_entries],
                hasher: ahash::RandomState::new(),
            };
            assert_eq!(merge.merge((a, b), size_log2), None);
            // The leaf fit; its parent must observe the newly exhausted limit.
            assert_eq!(mem.len(), last_available + 1);
            assert!(mem.exceeds_load_factor());
        }
    }

    #[test]
    fn final_merge_keeps_blank_and_cached_hits_available_at_capacity() {
        let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
        let mut blanks = BlankNodes::new();
        let size_log2 = LEAF_SIZE_LOG2 + 1;
        let blank = blanks.get_mut(size_log2, &mem);
        let a = mem.find_or_create_leaf_from_u64(1);
        let b = mem.find_or_create_leaf_from_u64(2);
        let a = mem.find_or_create_node(a, a, a, a);
        let b = mem.find_or_create_node(b, b, b, b);
        let mut merge = one_slot_merge(&mem, &blanks);
        let result = merge.merge((a, b), size_log2).unwrap();
        for cells in 0.. {
            if mem.exceeds_load_factor() {
                break;
            }
            mem.find_or_create_leaf_from_u64((1 << 63) | cells);
        }
        let full_len = mem.len();
        assert_eq!(merge.merge((a, b), size_log2), Some(result));
        assert_eq!(merge_final_universes(&mem, &blanks, (a, blank), size_log2), Some(a));
        assert_eq!(merge_final_universes(&mem, &blanks, (blank, b), size_log2), Some(b));
        assert_eq!(mem.len(), full_len);
    }

    #[test]
    fn final_merge_collisions_preserve_distinct_repeated_pairs() {
        let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
        let mut blanks = BlankNodes::new();
        let size_log2 = LEAF_SIZE_LOG2 + 2;
        let blank = blanks.get_mut(size_log2, &mem);
        let nodes = [1, 2, 4, 8].map(|cells| {
            let leaf = mem.find_or_create_leaf_from_u64(cells);
            mem.find_or_create_node(leaf, leaf, leaf, leaf)
        });
        let a = mem.find_or_create_node(nodes[0], nodes[1], nodes[0], nodes[1]);
        let b = mem.find_or_create_node(nodes[2], nodes[3], nodes[2], nodes[3]);
        let mut merge = one_slot_merge(&mem, &blanks);
        for pair in [(a, b), (b, a), (a, b), (a, blank), (blank, b)] {
            assert_eq!(
                merge.merge(pair, size_log2),
                Some(merge_universes(&mem, &blanks, pair, size_log2))
            );
        }
        for pair in [
            (nodes[0], nodes[2]),
            (nodes[1], nodes[3]),
            (nodes[0], nodes[2]),
        ] {
            assert_eq!(
                merge.merge(pair, size_log2 - 1),
                Some(merge_universes(&mem, &blanks, pair, size_log2 - 1))
            );
        }
    }

    #[test]
    #[should_panic(expected = "universes overlap")]
    fn final_merge_collision_does_not_hide_overlap() {
        let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
        let mut blanks = BlankNodes::new();
        let size_log2 = LEAF_SIZE_LOG2 + 1;
        blanks.get_mut(size_log2, &mem);
        let a = mem.find_or_create_leaf_from_u64(1);
        let b = mem.find_or_create_leaf_from_u64(2);
        let a = mem.find_or_create_node(a, a, a, a);
        let b = mem.find_or_create_node(b, b, b, b);
        let mut merge = one_slot_merge(&mem, &blanks);
        assert_eq!(
            merge.merge((a, b), size_log2),
            Some(merge_universes(&mem, &blanks, (a, b), size_log2))
        );
        merge.merge((a, a), size_log2);
    }

    #[test]
    #[should_panic(expected = "universes overlap")]
    fn final_merge_rejects_overlapping_shared_subtrees() {
        let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
        let mut blanks = BlankNodes::new();
        let size_log2 = LEAF_SIZE_LOG2 + 3;
        blanks.get_mut(size_log2, &mem);
        let mut root = mem.find_or_create_leaf_from_u64(1);
        for _ in LEAF_SIZE_LOG2..size_log2 {
            root = mem.find_or_create_node(root, root, root, root);
        }
        merge_final_universes(&mem, &blanks, (root, root), size_log2);
    }
}
