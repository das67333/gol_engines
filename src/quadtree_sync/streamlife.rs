use super::{
    hashlife::HashLifeEngineSync, CacheEntry, NodeIdx, QuadTreeNode, StreamLifeCache,
    LEAF_SIZE_LOG2,
};
use crate::{GoLEngine, Pattern, Topology};
use anyhow::{anyhow, Result};
use num_bigint::BigInt;

type MemoryManager = super::MemoryManager<u64>;

/// Implementation of [StreamLife algorithm](https://conwaylife.com/wiki/StreamLife).
///
/// It is build on top of [HashLifeEngineSync].
pub struct StreamLifeEngineSync {
    base: HashLifeEngineSync<u64>,
    // streamlife-specific
    biroot: Option<(NodeIdx, NodeIdx)>,
    bicache: StreamLifeCache,
}

impl StreamLifeEngineSync {
    fn determine_direction(&self, nw: NodeIdx, ne: NodeIdx, sw: NodeIdx, se: NodeIdx) -> u64 {
        let m = self.base.update_leaves(nw, ne, sw, se, 4);
        let centre = u64::from_le_bytes(self.base.mem.get(m).leaf_cells());

        let [nw, ne, sw, se] =
            [nw, ne, sw, se].map(|x| u64::from_le_bytes(self.base.mem.get(x).leaf_cells()));

        let z64_centre_to_u64 = |x, y| {
            let xs = (4 + x) as u64;
            let ys = ((4 + y) << 3) as u64;
            let bitmask: u64 = (0x0101010101010101 << xs) - 0x0101010101010101;
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

    fn node2lanes(&mut self, idx: NodeIdx, size_log2: u32) -> u64 {
        if idx == self.base.blank_nodes.get_mut(size_log2, &self.base.mem) {
            // blank node
            return 0xffff;
        }

        if size_log2 == LEAF_SIZE_LOG2 + 1 {
            let n = self.base.mem.get_mut(idx);
            if n.extra & 0xffff0000 != 1 << 16 {
                n.extra = self.determine_direction(n.nw, n.ne, n.sw, n.se) | (1 << 16);
            }
            return n.extra & 0xffffffff0000ffff;
        }

        let (nw, ne, sw, se, extra) = {
            let n = self.base.mem.get(idx);
            (n.nw, n.ne, n.sw, n.se, n.extra)
        };
        if (extra & 0xffff0000) != (1 << 16) {
            let mut childlanes = [0u64; 9];
            let mut adml: u64 = 0xff;
            /*
             * Short-circuit evaluation using the corner children
             * This will handle the vast majority of random tiles.
             */
            if adml != 0 {
                childlanes[0] = self.node2lanes(nw, size_log2 - 1);
                adml &= childlanes[0];
            }
            if adml != 0 {
                childlanes[2] = self.node2lanes(ne, size_log2 - 1);
                adml &= childlanes[2];
            }
            if adml != 0 {
                childlanes[6] = self.node2lanes(sw, size_log2 - 1);
                adml &= childlanes[6];
            }
            if adml != 0 {
                childlanes[8] = self.node2lanes(se, size_log2 - 1);
                adml &= childlanes[8];
            }
            if adml == 0 {
                self.base.mem.get_mut(idx).extra = 1 << 16;
                return 0;
            }

            if size_log2 == LEAF_SIZE_LOG2 + 2 {
                let tlx = {
                    let nw = self.base.mem.get(nw);
                    [nw.nw, nw.ne, nw.sw, nw.se]
                        .map(|x| u64::from_le_bytes(self.base.mem.get(x).leaf_cells()))
                };
                let trx = {
                    let ne = self.base.mem.get(ne);
                    [ne.nw, ne.ne, ne.sw, ne.se]
                        .map(|x| u64::from_le_bytes(self.base.mem.get(x).leaf_cells()))
                };
                let blx = {
                    let sw = self.base.mem.get(sw);
                    [sw.nw, sw.ne, sw.sw, sw.se]
                        .map(|x| u64::from_le_bytes(self.base.mem.get(x).leaf_cells()))
                };
                let brx = {
                    let se = self.base.mem.get(se);
                    [se.nw, se.ne, se.sw, se.se]
                        .map(|x| u64::from_le_bytes(self.base.mem.get(x).leaf_cells()))
                };

                let cc = [tlx[3], trx[2], blx[1], brx[0]];
                let tc = [tlx[1], trx[0], tlx[3], trx[2]];
                let bc = [blx[1], brx[0], blx[3], brx[2]];
                let cl = [tlx[2], tlx[3], blx[0], blx[1]];
                let cr = [trx[2], trx[3], brx[0], brx[1]];

                let prepared = |mem: &mut MemoryManager, x: &[u64; 4]| {
                    let nw = mem.find_or_create_leaf_from_u64(x[0]);
                    let ne = mem.find_or_create_leaf_from_u64(x[1]);
                    let sw = mem.find_or_create_leaf_from_u64(x[2]);
                    let se = mem.find_or_create_leaf_from_u64(x[3]);
                    mem.find_or_create_node(nw, ne, sw, se)
                };

                let x = prepared(&mut self.base.mem, &tc);
                childlanes[1] = self.node2lanes(x, LEAF_SIZE_LOG2 + 1);
                let x = prepared(&mut self.base.mem, &cl);
                childlanes[3] = self.node2lanes(x, LEAF_SIZE_LOG2 + 1);
                let x = prepared(&mut self.base.mem, &cc);
                childlanes[4] = self.node2lanes(x, LEAF_SIZE_LOG2 + 1);
                let x = prepared(&mut self.base.mem, &cr);
                childlanes[5] = self.node2lanes(x, LEAF_SIZE_LOG2 + 1);
                let x = prepared(&mut self.base.mem, &bc);
                childlanes[7] = self.node2lanes(x, LEAF_SIZE_LOG2 + 1);
                adml &=
                    childlanes[1] & childlanes[3] & childlanes[4] & childlanes[5] & childlanes[7];
            } else {
                let pptr_tl = self.base.mem.get(nw);
                let pptr_tr = self.base.mem.get(ne);
                let pptr_bl = self.base.mem.get(sw);
                let pptr_br = self.base.mem.get(se);
                let cc = [pptr_tl.se, pptr_tr.sw, pptr_bl.ne, pptr_br.nw];
                let tc = [pptr_tl.ne, pptr_tr.nw, pptr_tl.se, pptr_tr.sw];
                let bc = [pptr_bl.ne, pptr_br.nw, pptr_bl.se, pptr_br.sw];
                let cl = [pptr_tl.sw, pptr_tl.se, pptr_bl.nw, pptr_bl.ne];
                let cr = [pptr_tr.sw, pptr_tr.se, pptr_br.nw, pptr_br.ne];

                let prepared = |mem: &mut MemoryManager, x: &[NodeIdx; 4]| {
                    mem.find_or_create_node(x[0], x[1], x[2], x[3])
                };

                let x = prepared(&mut self.base.mem, &tc);
                childlanes[1] = self.node2lanes(x, size_log2 - 1);
                let x = prepared(&mut self.base.mem, &cl);
                childlanes[3] = self.node2lanes(x, size_log2 - 1);
                let x = prepared(&mut self.base.mem, &cc);
                childlanes[4] = self.node2lanes(x, size_log2 - 1);
                let x = prepared(&mut self.base.mem, &cr);
                childlanes[5] = self.node2lanes(x, size_log2 - 1);
                let x = prepared(&mut self.base.mem, &bc);
                childlanes[7] = self.node2lanes(x, size_log2 - 1);
                adml &=
                    childlanes[1] & childlanes[3] & childlanes[4] & childlanes[5] & childlanes[7];
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

            self.base.mem.get_mut(idx).extra = adml | (1 << 16) | (lanes << 32);
        }

        self.base.mem.get(idx).extra & 0xffffffff0000ffff
    }

    fn is_solitonic(&mut self, idx: (NodeIdx, NodeIdx), size_log2: u32) -> bool {
        let lanes1 = self.node2lanes(idx.0, size_log2);
        if lanes1 & 255 == 0 {
            return false;
        }
        let lanes2 = self.node2lanes(idx.1, size_log2);
        if lanes2 & 255 == 0 {
            return false;
        }
        let commonlanes = (lanes1 & lanes2) >> 32;
        if commonlanes != 0 {
            return false;
        }
        (((lanes1 >> 4) & lanes2) | ((lanes2 >> 4) & lanes1)) & 15 != 0
    }

    fn merge_universes(&mut self, idx: (NodeIdx, NodeIdx), size_log2: u32) -> NodeIdx {
        let b = self.base.blank_nodes.get_mut(size_log2, &self.base.mem);
        if idx.1 == b {
            return idx.0;
        }
        if idx.0 == b {
            return idx.1;
        }
        let m0 = self.base.mem.get(idx.0);
        let m1 = self.base.mem.get(idx.1);
        if size_log2 == LEAF_SIZE_LOG2 {
            let l0 = u64::from_le_bytes(m0.leaf_cells());
            let l1 = u64::from_le_bytes(m1.leaf_cells());
            debug_assert!(l0 & l1 == 0, "universes overlap");
            self.base.mem.find_or_create_leaf_from_u64(l0 | l1)
        } else {
            let (m0, m1) = (m0.parts(), m1.parts());
            let mut r = [NodeIdx::default(); 4];
            for i in 0..4 {
                r[i] = self.merge_universes((m0[i], m1[i]), size_log2 - 1);
            }
            self.base.mem.find_or_create_node(r[0], r[1], r[2], r[3])
        }
    }

    fn update_binode(&mut self, idx: (NodeIdx, NodeIdx), size_log2: u32) -> (NodeIdx, NodeIdx) {
        if self.bicache.is_poisoned() || self.base.mem.is_poisoned() {
            return (NodeIdx::default(), NodeIdx::default());
        }

        if self.is_solitonic(idx, size_log2) {
            let i1 = self.base.update_node(idx.0, size_log2);
            let i2 = self.base.update_node(idx.1, size_log2);

            let b = self.base.blank_nodes.get_mut(size_log2, &self.base.mem);
            return if idx.0 == b || idx.1 == b {
                let (i3, ind3) = if idx.0 == b {
                    (NodeIdx(i2.0), NodeIdx(idx.1 .0))
                } else {
                    (NodeIdx(i1.0), NodeIdx(idx.0 .0))
                };
                let lanes = self.node2lanes(ind3, size_log2);
                let b = self.base.blank_nodes.get_mut(size_log2 - 1, &self.base.mem);
                if lanes & 0xf0 != 0 {
                    (b, i3)
                } else {
                    (i3, b)
                }
            } else {
                (i1, i2)
            };
        }

        let (found, entry) = self.bicache.entry(idx);
        if found {
            return unsafe { (*entry).value };
        }

        let res = if size_log2 == LEAF_SIZE_LOG2 + 2 {
            let hnode2 = self.merge_universes(idx, size_log2);
            let i3 = self.base.update_node(hnode2, size_log2);
            let b = self.base.blank_nodes.get_mut(size_log2 - 1, &self.base.mem);

            if i3 != b {
                let lanes = self.node2lanes(hnode2, size_log2);
                if lanes & 0xf0 != 0 {
                    (b, i3)
                } else {
                    (i3, b)
                }
            } else {
                (b, b)
            }
        } else {
            let both_stages = self.base.generations_per_update_log2.unwrap() + 2 >= size_log2;

            let (mut arr90, mut arr91);
            if both_stages {
                let n0 = self.base.mem.get(idx.0);
                arr90 = self
                    .base
                    .nine_children_overlapping(n0.nw, n0.ne, n0.sw, n0.se);
                let n1 = self.base.mem.get(idx.1);
                arr91 = self
                    .base
                    .nine_children_overlapping(n1.nw, n1.ne, n1.sw, n1.se);
                for (l, r) in arr90.iter_mut().zip(arr91.iter_mut()) {
                    (*l, *r) = self.update_binode((*l, *r), size_log2 - 1);
                }
            } else {
                let n0 = self.base.mem.get(idx.0);
                arr90 = self
                    .base
                    .nine_children_disjoint(n0.nw, n0.ne, n0.sw, n0.se, size_log2 - 1);
                let n1 = self.base.mem.get(idx.1);
                arr91 = self
                    .base
                    .nine_children_disjoint(n1.nw, n1.ne, n1.sw, n1.se, size_log2 - 1);
            }

            let mut arr40 = self.base.four_children_overlapping(&arr90);
            let mut arr41 = self.base.four_children_overlapping(&arr91);

            for (l, r) in arr40.iter_mut().zip(arr41.iter_mut()) {
                (*l, *r) = self.update_binode((*l, *r), size_log2 - 1);
            }

            (
                self.base
                    .mem
                    .find_or_create_node(arr40[0], arr40[1], arr40[2], arr40[3]),
                self.base
                    .mem
                    .find_or_create_node(arr41[0], arr41[1], arr41[2], arr41[3]),
            )
        };

        unsafe { (*entry).value = res };
        res
    }

    fn add_frame(&mut self, dx: &mut BigInt, dy: &mut BigInt) {
        self.biroot = if let Some(biroot) = self.biroot {
            Some((
                self.base.with_frame(biroot.0, self.base.size_log2),
                self.base.with_frame(biroot.1, self.base.size_log2),
            ))
        } else {
            None
        };
        self.base.add_frame(dx, dy);
    }

    fn pop_frame(&mut self, dx: &mut BigInt, dy: &mut BigInt) {
        self.biroot = if let Some(biroot) = self.biroot {
            Some((
                self.base.without_frame(biroot.0),
                self.base.without_frame(biroot.1),
            ))
        } else {
            None
        };
        self.base.pop_frame(dx, dy);
    }
}

impl GoLEngine for StreamLifeEngineSync {
    fn new(mem_limit_mib: u32) -> Self {
        let nodes = ((mem_limit_mib as u64) << 20)
            / (std::mem::size_of::<QuadTreeNode<u64>>() + std::mem::size_of::<CacheEntry>()) as u64;
        // previous power of two
        let cap_log2 = (nodes / 2 + 1)
            .checked_next_power_of_two()
            .unwrap()
            .trailing_zeros();
        Self {
            base: HashLifeEngineSync::with_capacity(cap_log2),
            biroot: None,
            bicache: StreamLifeCache::with_capacity(cap_log2),
        }
    }

    fn load_pattern(&mut self, pattern: &Pattern, topology: Topology) -> Result<()> {
        self.base.load_pattern(pattern, topology)?;
        self.biroot = None;
        self.bicache.clear();
        Ok(())
    }

    fn current_state(&self) -> Pattern {
        self.base.current_state()
    }

    fn update(&mut self, generations_log2: u32) -> Result<[BigInt; 2]> {
        if let Some(cached_generations_log2) = self.base.generations_per_update_log2 {
            if cached_generations_log2 != generations_log2 {
                self.run_gc();
            }
        }
        let backup = self.current_state();
        self.base.generations_per_update_log2 = Some(generations_log2);

        let frames_cnt = (generations_log2 + 2).max(self.base.size_log2 + 1) - self.base.size_log2;
        let (mut dx, mut dy) = (BigInt::ZERO, BigInt::ZERO);
        for _ in 0..frames_cnt {
            self.add_frame(&mut dx, &mut dy);
        }

        let biroot = self.biroot.unwrap_or((
            self.base.root,
            self.base
                .blank_nodes
                .get_mut(self.base.size_log2, &self.base.mem),
        ));
        let biroot = self.update_binode(biroot, self.base.size_log2);
        if self.bicache.is_poisoned() || self.base.mem.is_poisoned() {
            self.load_pattern(&backup, self.base.topology)?;
            return Err(anyhow!(
                "StreamLifeSync: overfilled MemoryManager, try smaller step"
            ));
        }

        self.base.size_log2 -= 1;
        self.biroot = Some(biroot);
        self.base.root = self.merge_universes(biroot, self.base.size_log2);
        dx -= BigInt::from(1) << (self.base.size_log2 - 1);
        dy -= BigInt::from(1) << (self.base.size_log2 - 1);

        match self.base.topology {
            Topology::Torus => {
                for _ in 0..frames_cnt - 1 {
                    self.pop_frame(&mut dx, &mut dy);
                }
            }
            Topology::Unbounded => {
                while self.base.has_blank_frame() {
                    self.pop_frame(&mut dx, &mut dy);
                }
            }
        }

        Ok([dx, dy])
    }

    fn run_gc(&mut self) {
        self.bicache.clear();
        self.biroot = None;
        self.base.run_gc();
    }

    fn bytes_total(&self) -> usize {
        self.base.bytes_total() + self.bicache.bytes_total()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const SEED: u64 = 42;

    #[test]
    fn test_pattern_roundtrip() {
        for size_log2 in 3..10 {
            let original = Pattern::random(size_log2, Some(SEED)).unwrap();
            let mut engine = StreamLifeEngineSync::new(2);
            engine.load_pattern(&original, Topology::Unbounded).unwrap();
            let converted = engine.current_state();

            assert_eq!(
                original.hash(),
                converted.hash(),
                "Pattern roundtrip failed for size 2^{}",
                size_log2
            );
        }
    }
}
