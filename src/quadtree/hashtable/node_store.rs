use super::{
    super::{
        node::QuadTreeNode,
        parallel_executors::{GcMarkExecutor, GcMarkOptions, GcSweepExecutor},
        sharded_statistics::LengthShard,
        status,
    },
    base::{ConcurrentHashTable, Idx, NULL_IDX, compute_hash},
};
use std::sync::atomic::Ordering;

/// Shared interface for accessing nodes.
pub trait NodeAccess<Meta: Default + Sync> {
    fn should_stop(&self) -> bool;
    fn get(&self, idx: Idx) -> &QuadTreeNode<Meta>;
    fn find_or_create_node(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> Idx;
    fn find_or_create_leaf_from_u64(&self, value: u64) -> Idx;
    fn find_or_create_leaf_from_parts(&self, nw: u16, ne: u16, sw: u16, se: u16) -> Idx;
}

/// Per-thread reference to a store that uses local sharding for length
/// tracking *and* per-thread chunk allocation.
pub struct ShardedRef<'a, S> {
    pub base: &'a S,
    pub shard_idx: usize,
    pub length_shard: LengthShard<'a>,
}

/// Type alias for per-thread `NodeStore` references.
pub type NodeStoreRef<'a, Meta> = ShardedRef<'a, NodeStore<Meta>>;

/// Stores the nodes of the quadtree.
pub struct NodeStore<Meta> {
    inner: ConcurrentHashTable<QuadTreeNode<Meta>>,
    pub(in crate::quadtree) cancellation: crate::CancellationToken,
}

unsafe impl<Meta: Sync> Sync for NodeStore<Meta> {}

impl<Meta: Default + Sync> NodeAccess<Meta> for NodeStore<Meta> {
    fn should_stop(&self) -> bool {
        self.should_stop()
    }
    fn get(&self, idx: Idx) -> &QuadTreeNode<Meta> {
        self.get(idx)
    }
    fn find_or_create_node(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> Idx {
        self.find_or_create_node(nw, ne, sw, se)
    }
    fn find_or_create_leaf_from_u64(&self, value: u64) -> Idx {
        self.find_or_create_leaf_from_u64(value)
    }
    fn find_or_create_leaf_from_parts(&self, nw: u16, ne: u16, sw: u16, se: u16) -> Idx {
        self.find_or_create_leaf_from_parts(nw, ne, sw, se)
    }
}

impl<Meta: Default + Sync> NodeStore<Meta> {
    pub fn new(cap_log2: u32, entry_capacity: usize, threads_cnt: usize) -> Self {
        Self {
            inner: ConcurrentHashTable::new(cap_log2, entry_capacity, threads_cnt),
            cancellation: crate::CancellationToken::default(),
        }
    }

    pub fn get(&self, idx: Idx) -> &QuadTreeNode<Meta> {
        self.inner.get(idx)
    }

    /// Find a leaf node with the given parts (4×4 grids as 16-bit integers).
    pub fn find_or_create_leaf_from_parts(&self, nw: u16, ne: u16, sw: u16, se: u16) -> Idx {
        let (result, inserted) = self.find_or_create_leaf_from_parts_inner(0, nw, ne, sw, se);
        if inserted {
            self.inner.increment_length();
        }
        result
    }

    fn find_or_create_leaf_from_parts_inner(
        &self,
        shard_idx: usize,
        nw: u16,
        ne: u16,
        sw: u16,
        se: u16,
    ) -> (Idx, bool) {
        // See Morton order: https://en.wikipedia.org/wiki/Z-order_curve
        let (mut nw, mut ne) = (u64::from(nw), u64::from(ne));
        let mut cells = 0;
        let mut shift = 0;
        for _ in 0..4 {
            cells |= (nw & 0xF) << shift;
            nw >>= 4;
            shift += 4;
            cells |= (ne & 0xF) << shift;
            ne >>= 4;
            shift += 4;
        }
        let (mut sw, mut se) = (u64::from(sw), u64::from(se));
        for _ in 0..4 {
            cells |= (sw & 0xF) << shift;
            sw >>= 4;
            shift += 4;
            cells |= (se & 0xF) << shift;
            se >>= 4;
            shift += 4;
        }

        self.find_or_create_leaf_from_u64_inner(shard_idx, cells)
    }

    /// Find a leaf node with the given cells (8×8 grid as 64-bit integer).
    pub fn find_or_create_leaf_from_u64(&self, value: u64) -> Idx {
        let (result, inserted) = self.find_or_create_leaf_from_u64_inner(0, value);
        if inserted {
            self.inner.increment_length();
        }
        result
    }

    fn find_or_create_leaf_from_u64_inner(&self, shard_idx: usize, value: u64) -> (Idx, bool) {
        let rows = value.to_le_bytes();
        let nw = u32::from_le_bytes(rows[0..4].try_into().unwrap());
        let ne = u32::from_le_bytes(rows[4..8].try_into().unwrap());
        // Leaves: sw == 0 && se == 0 (the leaf marker; see node.rs docs).
        let hash = compute_hash(nw, ne, 0, 0);
        self.inner.find_or_create(
            hash,
            shard_idx,
            |slot| (slot.nw, slot.ne, slot.sw, slot.se) == (nw, ne, 0, 0),
            |slot| unsafe {
                (*slot).nw = nw;
                (*slot).ne = ne;
                (*slot).sw = 0;
                (*slot).se = 0;
            },
        )
    }

    /// Find a node with the given children. If not found, it is created.
    pub fn find_or_create_node(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> Idx {
        let (result, inserted) = self.find_or_create_node_inner(0, nw, ne, sw, se);
        if inserted {
            self.inner.increment_length();
        }
        result
    }

    fn find_or_create_node_inner(
        &self,
        shard_idx: usize,
        nw: Idx,
        ne: Idx,
        sw: Idx,
        se: Idx,
    ) -> (Idx, bool) {
        assert!(
            nw != NULL_IDX && ne != NULL_IDX && sw != NULL_IDX && se != NULL_IDX,
            "internal nodes must have non-null children (Idx 0 = null); got nw={nw} ne={ne} sw={sw} se={se}"
        );
        let hash = compute_hash(nw, ne, sw, se);
        self.inner.find_or_create(
            hash,
            shard_idx,
            |slot| (slot.nw, slot.ne, slot.sw, slot.se) == (nw, ne, sw, se),
            |slot| unsafe {
                (*slot).nw = nw;
                (*slot).ne = ne;
                (*slot).sw = sw;
                (*slot).se = se;
            },
        )
    }

    pub fn create_ref(&self, shard_idx: usize) -> NodeStoreRef<'_, Meta> {
        ShardedRef {
            base: self,
            shard_idx,
            length_shard: self.inner.shard(shard_idx),
        }
    }

    pub fn clear(&mut self) {
        self.inner.clear();
    }

    pub fn bytes_total(&self) -> usize {
        self.inner.bytes_total()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// See [`ConcurrentHashTable::for_each_idx`]. Single-threaded use only.
    pub fn for_each_idx(&self, f: impl FnMut(Idx)) {
        self.inner.for_each_idx(f);
    }

    pub fn exceeds_load_factor(&self) -> bool {
        self.inner.exceeds_load_factor()
    }

    pub fn should_stop(&self) -> bool {
        self.exceeds_load_factor() || self.cancellation.is_cancelled()
    }

    /// Parallel mark-and-sweep GC. Marks all nodes reachable from `roots`
    /// using a status bit (`GC_MARK`), then recycles dead entries in parallel.
    /// Cached computation results are invalidated.
    pub fn gc(&mut self, roots: &[(Idx, u32)]) {
        self.mark(roots, false);
        self.sweep(false);
    }

    /// If requested, follow completed results; the caller must keep their
    /// update-size context valid. Preserving work also requires marking every
    /// pending input, intermediate node, and unconsumed result.
    pub fn mark(&self, roots: &[(Idx, u32)], retain_results: bool) {
        let threads_cnt = self.inner.thread_states.len();
        GcMarkExecutor::new(self, roots, GcMarkOptions { threads_cnt, retain_results }).run();
    }

    pub fn sweep(&mut self, retain_results: bool) {
        // Sweep removes unmarked entries and clears transient status bits.
        // We intentionally leave
        // `status_extra` and `extra` (StreamLife lane data) untouched —
        // they depend only on cell structure, which is immutable for a given Idx.
        GcSweepExecutor::new(&mut self.inner).run(|entry| {
            let old = entry.status.load(Ordering::Relaxed);
            if old & status::GC_MARK == 0 {
                assert_eq!(old & status::PENDING, 0, "pending node was not rooted");
                return true;
            }
            let retained = if retain_results { old & (status::FINISHED | status::PENDING) } else { status::NOT_STARTED };
            entry.status.store(retained, Ordering::Relaxed);
            false
        });
    }
}

impl<Meta: Default + Sync> NodeStoreRef<'_, Meta> {
    pub fn get(&self, idx: Idx) -> &QuadTreeNode<Meta> {
        self.base.get(idx)
    }

    pub fn find_or_create_leaf_from_parts(&self, nw: u16, ne: u16, sw: u16, se: u16) -> Idx {
        let (result, inserted) =
            self.base
                .find_or_create_leaf_from_parts_inner(self.shard_idx, nw, ne, sw, se);
        if inserted {
            self.length_shard.increment();
        }
        result
    }

    pub fn find_or_create_leaf_from_u64(&self, value: u64) -> Idx {
        let (result, inserted) = self
            .base
            .find_or_create_leaf_from_u64_inner(self.shard_idx, value);
        if inserted {
            self.length_shard.increment();
        }
        result
    }

    pub fn find_or_create_node(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> Idx {
        let (result, inserted) =
            self.base
                .find_or_create_node_inner(self.shard_idx, nw, ne, sw, se);
        if inserted {
            self.length_shard.increment();
        }
        result
    }
}

impl<Meta: Default + Sync> NodeAccess<Meta> for NodeStoreRef<'_, Meta> {
    fn should_stop(&self) -> bool {
        self.base.should_stop()
    }
    fn get(&self, idx: Idx) -> &QuadTreeNode<Meta> {
        self.get(idx)
    }
    fn find_or_create_node(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> Idx {
        self.find_or_create_node(nw, ne, sw, se)
    }
    fn find_or_create_leaf_from_u64(&self, value: u64) -> Idx {
        self.find_or_create_leaf_from_u64(value)
    }
    fn find_or_create_leaf_from_parts(&self, nw: u16, ne: u16, sw: u16, se: u16) -> Idx {
        self.find_or_create_leaf_from_parts(nw, ne, sw, se)
    }
}

#[cfg(test)]
mod tests;
