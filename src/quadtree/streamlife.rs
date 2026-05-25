use super::{
    algorithm,
    hashlife::HashLifeEngine,
    hashtable::{BinodeCache, CacheEntry, Idx},
    node::QuadTreeNode,
    parallel_executors::StreamLifeExecutor,
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
        // Memory accounting: NodeStore<u64> and BinodeCache share the same
        // `bucket_count`. Per-bucket cost = (bucket_head + node body) +
        // (bucket_head + cache entry).
        let mem_bytes = (mem_limit_mib as u64) << 20;
        let per_bucket = std::mem::size_of::<std::sync::atomic::AtomicU32>()
            + std::mem::size_of::<QuadTreeNode<u64>>()
            + std::mem::size_of::<std::sync::atomic::AtomicU32>()
            + std::mem::size_of::<CacheEntry>();
        let max_buckets = (mem_bytes / per_bucket as u64).max(1);
        let cap_log2 = max_buckets.ilog2();
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
        if self
            .base
            .generations_per_update_log2
            .is_some_and(|g| g != generations_log2)
        {
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

        let Some(biroot) =
            StreamLifeExecutor::new(self, biroot, self.base.size_log2).run(self.base.threads_cnt)
        else {
            self.load_pattern(&backup, self.base.topology)?;
            return Err(anyhow!(
                "StreamLife: overfilled NodeStore or BinodeCache, try smaller step"
            ));
        };

        self.base.size_log2 -= 1;
        self.biroot = Some(biroot);
        self.base.root = algorithm::merge_universes(
            &self.base.mem,
            &self.base.blank_nodes,
            biroot,
            self.base.size_log2,
        );
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
        let nodes_before = self.base.mem.len();
        let bicache_before = self.bicache.len();
        let t = std::time::Instant::now();
        self.bicache.clear();
        self.biroot = None;
        self.base.run_gc();
        let elapsed = t.elapsed();
        let nodes_after = self.base.mem.len();
        println!(
            "StreamLife GC: {:?}  nodes {} → {} (freed {:.2}%)  bicache {} → 0",
            elapsed,
            nodes_before,
            nodes_after,
            100. * (1. - nodes_after as f64 / nodes_before as f64),
            bicache_before,
        );
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
