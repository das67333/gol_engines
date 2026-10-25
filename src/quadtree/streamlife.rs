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
    // Balance the stores by bytes. Buckets are powers of two; entry storage uses the remainder.
    // This accounts for buckets and live entries, excluding allocator chunk slack and metadata.
    fn capacity_plan(mem_limit_mib: u32) -> (u32, usize, u32, usize) {
        let budget = u64::from(mem_limit_mib) << 20;
        let bucket_bytes = std::mem::size_of::<std::sync::atomic::AtomicU32>() as u64;
        let node_entry_bytes = std::mem::size_of::<QuadTreeNode<u64>>() as u64;
        let cache_entry_bytes = std::mem::size_of::<CacheEntry>() as u64;
        let node_bytes = bucket_bytes + node_entry_bytes;
        let cache_bytes = bucket_bytes + cache_entry_bytes;
        let mut best = (0, 0);
        let mut score = (0, 0);
        for node_log in 0..=32 {
            for cache_log in 0..=32 {
                let nodes = node_bytes << node_log;
                let cache = cache_bytes << cache_log;
                let candidate = (nodes.min(cache), nodes + cache);
                if nodes + cache <= budget && candidate > score {
                    best = (node_log, cache_log);
                    score = candidate;
                }
            }
        }
        let node_buckets = 1u64 << best.0;
        let cache_buckets = 1u64 << best.1;
        let minimum_nodes = node_bytes * node_buckets;
        let minimum_cache = cache_bytes * cache_buckets;
        let budget = budget.max(minimum_nodes + minimum_cache);
        let node_budget = (budget / 2).clamp(minimum_nodes, budget - minimum_cache);
        let node_capacity = (node_budget - bucket_bytes * node_buckets) / node_entry_bytes;
        let cache_capacity =
            (budget - node_budget - bucket_bytes * cache_buckets) / cache_entry_bytes;
        (
            best.0,
            node_capacity as usize,
            best.1,
            cache_capacity as usize,
        )
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
        let (node_log, node_capacity, cache_log, cache_capacity) =
            Self::capacity_plan(mem_limit_mib);
        Self {
            base: HashLifeEngine::<u64>::with_capacity(node_log, node_capacity, threads_cnt),
            biroot: None,
            bicache: BinodeCache::new(cache_log, cache_capacity, threads_cnt),
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
    fn test_capacity_plan() {
        for (gib, expected) in [
            (20, (28, 28)),
            (32, (28, 29)),
            (48, (29, 29)),
            (64, (29, 30)),
            (128, (30, 31)),
        ] {
            let (node_log, node_capacity, cache_log, cache_capacity) =
                StreamLifeEngine::capacity_plan(gib * 1024);
            assert_eq!((node_log, cache_log), expected);
            assert!(node_capacity >= 1usize << node_log);
            assert!(cache_capacity >= 1usize << cache_log);
            let bytes = 4 * ((1u64 << node_log) + (1u64 << cache_log))
                + node_capacity as u64 * std::mem::size_of::<QuadTreeNode<u64>>() as u64
                + cache_capacity as u64 * std::mem::size_of::<CacheEntry>() as u64;
            assert!(bytes <= u64::from(gib) << 30);
            assert!((u64::from(gib) << 30) - bytes < 64);
        }
    }

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
