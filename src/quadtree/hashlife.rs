use super::{
    LEAF_SIZE_LOG2,
    blank::BlankNodes,
    hashlife_executor::HashLifeExecutor,
    hashtable::{Idx, NodeStore},
    node::QuadTreeNode,
};
use crate::{GoLEngine, Pattern, PatternNode, Topology};
use ahash::AHashMap as HashMap;
use anyhow::{Result, anyhow};
use num_bigint::BigInt;

/// Parallel implementation of [HashLife algorithm](https://conwaylife.com/wiki/HashLife).
///
/// Stores nodes in a single pre-allocated open-addressing hashtable with
/// linear probing, and the hashtable never grows.
pub struct HashLifeEngine<Meta> {
    pub(super) size_log2: u32,
    pub(super) root: Idx,
    pub(super) mem: NodeStore<Meta>,
    pub(super) generations_per_update_log2: Option<u32>,
    pub(super) topology: Topology,
    pub(super) blank_nodes: BlankNodes,
    pub(super) threads_cnt: usize,
}

impl<Meta: Default + Sync> HashLifeEngine<Meta> {
    /// Add a frame around the field: if `self.topology` is Unbounded, frame is blank,
    /// and if `self.topology` is Torus, frame mirrors the field.
    /// The field becomes two times bigger.
    pub(super) fn with_frame(&mut self, idx: Idx, size_log2: u32) -> Idx {
        let n = self.mem.get(idx);
        let b = self.blank_nodes.get_mut(size_log2 - 1, &self.mem);
        let [nw, ne, sw, se] = match self.topology {
            Topology::Torus => [self.mem.find_or_create_node(n.se, n.sw, n.ne, n.nw); 4],
            Topology::Unbounded => [
                self.mem.find_or_create_node(b, b, b, n.nw),
                self.mem.find_or_create_node(b, b, n.ne, b),
                self.mem.find_or_create_node(b, n.sw, b, b),
                self.mem.find_or_create_node(n.se, b, b, b),
            ],
        };
        self.mem.find_or_create_node(nw, ne, sw, se)
    }

    /// Remove a frame around the field, making it two times smaller.
    pub(super) fn without_frame(&self, idx: Idx) -> Idx {
        let [nw, ne, sw, se] = self.mem.get(idx).parts().map(|x| self.mem.get(x));
        self.mem.find_or_create_node(nw.se, ne.sw, sw.ne, se.nw)
    }

    pub(super) fn has_blank_frame(&mut self) -> bool {
        if self.size_log2 <= LEAF_SIZE_LOG2 + 1 {
            return false;
        }

        let b = self.blank_nodes.get_mut(self.size_log2 - 2, &self.mem);

        let root = self.mem.get(self.root);
        let [nw, ne, sw, se] = [
            self.mem.get(root.nw),
            self.mem.get(root.ne),
            self.mem.get(root.sw),
            self.mem.get(root.se),
        ];
        let frame_parts = [
            nw.sw, nw.nw, nw.ne, ne.nw, ne.ne, ne.se, se.ne, se.se, se.sw, sw.se, sw.sw, sw.nw,
        ];
        frame_parts.iter().all(|&x| x == b)
    }

    pub(super) fn add_frame(&mut self, dx: &mut BigInt, dy: &mut BigInt) {
        self.root = self.with_frame(self.root, self.size_log2);
        *dx += BigInt::from(1) << (self.size_log2 - 1);
        *dy += BigInt::from(1) << (self.size_log2 - 1);
        self.size_log2 += 1;
    }

    pub(super) fn pop_frame(&mut self, dx: &mut BigInt, dy: &mut BigInt) {
        self.root = self.without_frame(self.root);
        *dx -= BigInt::from(1) << (self.size_log2 - 2);
        *dy -= BigInt::from(1) << (self.size_log2 - 2);
        self.size_log2 -= 1;
    }

    fn init_pattern_recursive(
        idx: u32,
        pattern: &Pattern,
        mem: &NodeStore<Meta>,
        cache: &mut HashMap<u32, Idx>,
    ) -> Idx {
        if let Some(&cached) = cache.get(&idx) {
            return cached;
        }
        let result = match pattern.get_node(idx) {
            PatternNode::Leaf(cells) => mem.find_or_create_leaf_from_u64(*cells),
            PatternNode::Node { nw, ne, sw, se } => mem.find_or_create_node(
                Self::init_pattern_recursive(*nw, pattern, mem, cache),
                Self::init_pattern_recursive(*ne, pattern, mem, cache),
                Self::init_pattern_recursive(*sw, pattern, mem, cache),
                Self::init_pattern_recursive(*se, pattern, mem, cache),
            ),
        };
        cache.insert(idx, result);
        result
    }

    pub(super) fn with_capacity(cap_log2: u32, threads_cnt: usize) -> Self {
        let mem = NodeStore::new(cap_log2, threads_cnt);
        Self {
            size_log2: LEAF_SIZE_LOG2,
            root: mem.find_or_create_leaf_from_u64(0),
            mem,
            generations_per_update_log2: None,
            topology: Topology::Unbounded,
            blank_nodes: BlankNodes::new(),
            threads_cnt,
        }
    }
}

impl<Meta: Default + Sync> GoLEngine for HashLifeEngine<Meta> {
    fn new(mem_limit_mib: u32, threads_cnt: usize) -> Self {
        // Memory accounting: at full load (load factor = 1) the table holds
        // `bucket_count` nodes plus a `bucket_count`-sized array of bucket
        // heads. Per-bucket cost: one `AtomicU32` (4 B) plus one node body.
        // We pick the largest power-of-2 `bucket_count` fitting the budget.
        let mem_bytes = (mem_limit_mib as u64) << 20;
        let per_bucket = std::mem::size_of::<std::sync::atomic::AtomicU32>()
            + std::mem::size_of::<QuadTreeNode<Meta>>();
        let max_buckets = (mem_bytes / per_bucket as u64).max(1);
        let cap_log2 = max_buckets.ilog2();
        Self::with_capacity(cap_log2, threads_cnt)
    }

    fn load_pattern(&mut self, pattern: &Pattern, topology: Topology) -> Result<()> {
        let size_log2 = pattern.get_size_log2();
        if size_log2 < LEAF_SIZE_LOG2 {
            return Err(anyhow!("Pattern is too small"));
        }
        self.size_log2 = size_log2;
        self.mem.clear();
        self.blank_nodes.clear();
        let mut cache = HashMap::new();
        self.root =
            Self::init_pattern_recursive(pattern.get_root(), pattern, &self.mem, &mut cache);
        self.generations_per_update_log2 = None;
        self.topology = topology;
        Ok(())
    }

    fn current_state(&self) -> Pattern {
        fn inner<Meta: Default + Sync>(
            idx: Idx,
            size_log2: u32,
            mem: &NodeStore<Meta>,
            pattern: &mut Pattern,
            cache: &mut HashMap<Idx, u32>,
        ) -> u32 {
            if let Some(&cached) = cache.get(&idx) {
                return cached;
            }
            let n = mem.get(idx);
            let result = if size_log2 == LEAF_SIZE_LOG2 {
                let cells = u64::from_le_bytes(n.leaf_cells());
                pattern.find_or_create_node(PatternNode::Leaf(cells))
            } else {
                let [nw, ne, sw, se] = n
                    .parts()
                    .map(|x| inner(x, size_log2 - 1, mem, pattern, cache));
                pattern.find_or_create_node(PatternNode::Node { nw, ne, sw, se })
            };
            cache.insert(idx, result);
            result
        }

        let mut cache = HashMap::new();
        let mut pattern = Pattern::new(Some(self.size_log2));
        let root = inner(
            self.root,
            self.size_log2,
            &self.mem,
            &mut pattern,
            &mut cache,
        );
        unsafe { pattern.change_root(root, self.size_log2) };
        pattern
    }

    fn update(&mut self, generations_log2: u32) -> Result<[BigInt; 2]> {
        if self.generations_per_update_log2 != Some(generations_log2) {
            self.run_gc();
        }
        let backup = self.current_state();
        self.generations_per_update_log2 = Some(generations_log2);

        let frames_cnt = (generations_log2 + 2).max(self.size_log2 + 1) - self.size_log2;
        let (mut dx, mut dy) = (BigInt::ZERO, BigInt::ZERO);
        for _ in 0..frames_cnt {
            self.add_frame(&mut dx, &mut dy);
        }

        // let mut builder = tokio::runtime::Builder::new_multi_thread();
        // if num_threads > 0 {
        //     builder.worker_threads(num_threads as usize);
        // }

        // builder
        //     .build()
        //     .unwrap()
        //     .block_on(async { self.update_node_async(self.root, self.size_log2).await })
        // self.update_node_sync(self.root, self.size_log2)
        self.root = if let Some(x) = HashLifeExecutor::new(self).run(self.threads_cnt) {
            x
        } else {
            self.load_pattern(&backup, self.topology)?;
            return Err(anyhow!(
                "HashLifeAsync: overfilled NodeStore, try smaller step"
            ));
        };

        self.size_log2 -= 1;
        dx -= BigInt::from(1) << (self.size_log2 - 1);
        dy -= BigInt::from(1) << (self.size_log2 - 1);

        match self.topology {
            Topology::Torus => {
                for _ in 0..frames_cnt - 1 {
                    self.pop_frame(&mut dx, &mut dy);
                }
            }
            Topology::Unbounded => {
                while self.has_blank_frame() {
                    self.pop_frame(&mut dx, &mut dy);
                }
            }
        }

        Ok([dx, dy])
    }

    fn run_gc(&mut self) {
        let pattern = self.current_state();
        self.mem.clear();
        self.blank_nodes.clear();
        let mut cache = HashMap::new();
        self.root =
            Self::init_pattern_recursive(pattern.get_root(), &pattern, &self.mem, &mut cache);
        self.generations_per_update_log2 = None;
    }

    fn bytes_total(&self) -> usize {
        self.mem.bytes_total()
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
            let mut engine = HashLifeEngine::<()>::new(1, 1);
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
