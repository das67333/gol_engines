use super::{
    LEAF_SIZE_LOG2, algorithm,
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
    fn reset_stream_cache(&mut self) {
        self.biroot = None;
        self.bicache.clear();
    }

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

    fn add_frame(&mut self, dx: &mut BigInt, dy: &mut BigInt) -> Option<()> {
        // At most five nodes per framed root, plus every blank level through
        // the new root. This also covers the executor's root blank if its chain was empty.
        let framed_roots = if self.biroot.is_some() { 3 } else { 1 };
        let frame_allocations = framed_roots * 5 + (self.base.size_log2 - LEAF_SIZE_LOG2) as usize + 2;
        if self.base.mem.capacity().saturating_sub(self.base.mem.len()) < frame_allocations {
            return None;
        }
        self.biroot = if let Some(biroot) = self.biroot {
            Some((
                self.base.with_frame(biroot.0, self.base.size_log2),
                self.base.with_frame(biroot.1, self.base.size_log2),
            ))
        } else {
            None
        };
        self.base.add_frame(dx, dy);
        Some(())
    }

    fn pop_frame(&mut self, dx: &mut BigInt, dy: &mut BigInt) -> Option<()> {
        // At most three nodes are allocated; the worker cancellation reserve
        // covers this burst. All queried blank levels were initialized before the executor.
        if self.base.mem.exceeds_load_factor() {
            return None;
        }
        self.biroot = if let Some(biroot) = self.biroot {
            Some((
                self.base.without_frame(biroot.0),
                self.base.without_frame(biroot.1),
            ))
        } else {
            None
        };
        self.base.pop_frame(dx, dy);
        Some(())
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
        self.reset_stream_cache();
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
        let (root, size_log2) = (self.base.root, self.base.size_log2);
        self.base.generations_per_update_log2 = Some(generations_log2);

        let result = (|| {
            let frames_cnt = self.base.frames_for_update(generations_log2);
            let (mut dx, mut dy) = (BigInt::ZERO, BigInt::ZERO);
            for _ in 0..frames_cnt {
                self.add_frame(&mut dx, &mut dy)?;
            }

            let biroot = self.biroot.unwrap_or((
                self.base.root,
                // It guarantees that blank_nodes doesn't mutate during the executor.
                self.base.blank_nodes.get_mut(self.base.size_log2, &self.base.mem),
            ));
            let biroot = StreamLifeExecutor::new(self, biroot, self.base.size_log2).run(self.base.threads_cnt)?;
            let new_size_log2 = self.base.size_log2 - 1;
            let new_root = algorithm::merge_final_universes(
                &self.base.mem,
                &self.base.blank_nodes,
                biroot,
                new_size_log2,
            )?;

            self.base.size_log2 = new_size_log2;
            self.biroot = Some(biroot);
            self.base.root = new_root;
            dx -= BigInt::from(1) << (self.base.size_log2 - 1);
            dy -= BigInt::from(1) << (self.base.size_log2 - 1);

            match self.base.topology {
                Topology::Torus => {
                    for _ in 0..frames_cnt - 1 {
                        self.pop_frame(&mut dx, &mut dy)?;
                    }
                }
                Topology::Unbounded => {
                    while self.base.has_blank_frame() {
                        self.pop_frame(&mut dx, &mut dy)?;
                    }
                }
            }
            Some([dx, dy])
        })();

        if let Some(offset) = result {
            return Ok(offset);
        }
        // All phases leave structural nodes intact; serialize rollback only on failure.
        self.base.root = root;
        self.base.size_log2 = size_log2;
        self.reset_stream_cache();
        let backup = self.current_state();
        self.base.load_pattern(&backup, self.base.topology)?;
        Err(anyhow!("StreamLife: overfilled NodeStore or BinodeCache, try smaller step"))
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
mod tests;
