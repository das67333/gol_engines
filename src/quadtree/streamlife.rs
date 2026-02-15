use super::{
    LEAF_SIZE_LOG2,
    executor::Executor,
    hashlife::HashLifeEngine,
    hashtable::{BinodeCache, CacheEntry, Idx},
    node::QuadTreeNode,
};
use crate::{GoLEngine, Pattern, Topology};
use anyhow::{Result, anyhow};
use num_bigint::BigInt;

/// Implementation of [StreamLife algorithm](https://conwaylife.com/wiki/StreamLife).
///
/// Built on top of [`HashLifeEngine`]. Uses a static hashtable for caching
/// results of `update_binode` function.
pub struct StreamLifeEngine {
    pub(super) base: HashLifeEngine<u64>,
    // streamlife-specific
    biroot: Option<(Idx, Idx)>,
    pub(super) bicache: BinodeCache,
}

impl StreamLifeEngine {
    /// Merge two non-overlapping universes into a single node. Thread-safe.
    pub(super) fn merge_universes(&self, idx: (Idx, Idx), size_log2: u32) -> Idx {
        let b = self.base.blank_nodes.get(size_log2);
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
            let mut r = [Idx::default(); 4];
            for i in 0..4 {
                r[i] = self.merge_universes((m0[i], m1[i]), size_log2 - 1);
            }
            self.base.mem.find_or_create_node(r[0], r[1], r[2], r[3])
        }
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

impl GoLEngine for StreamLifeEngine {
    fn new(mem_limit_mib: u32, threads_cnt: usize) -> Self {
        let nodes = ((mem_limit_mib as u64) << 20)
            / (std::mem::size_of::<QuadTreeNode<u64>>() + std::mem::size_of::<CacheEntry>()) as u64;
        // previous power of two
        let cap_log2 = (nodes / 2 + 1)
            .checked_next_power_of_two()
            .unwrap()
            .trailing_zeros();
        Self {
            base: HashLifeEngine::<u64>::with_capacity(cap_log2, threads_cnt),
            biroot: None,
            bicache: BinodeCache::new(cap_log2, threads_cnt),
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
        if self.base.generations_per_update_log2 != Some(generations_log2) {
            self.run_gc();
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
            // it guarantees that self.base.blank_nodes doesn't mutate during the update
            self.base
                .blank_nodes
                .get_mut(self.base.size_log2, &self.base.mem),
        ));

        let biroot = if let Some(x) = Executor::new_streamlife(self, biroot, self.base.size_log2)
            .run_streamlife(self.base.threads_cnt)
        {
            x
        } else {
            self.load_pattern(&backup, self.base.topology)?;
            return Err(anyhow!(
                "StreamLife: overfilled NodeStore or BinodeCache, try smaller step"
            ));
        };

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
            let mut engine = StreamLifeEngine::new(1, 1);
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
