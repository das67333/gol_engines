use super::{
    super::{LEAF_SIZE_LOG2, node::QuadTreeNode, sharded_statistics::LengthShard, status},
    base::{ConcurrentHashTable, Idx, NULL_IDX, compute_hash},
};
use ahash::AHashSet;
use std::sync::atomic::Ordering;

/// Shared interface for accessing nodes.
pub trait NodeAccess<Meta: Default + Sync> {
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

/// Type alias for per-thread NodeStore references.
pub type NodeStoreRef<'a, Meta> = ShardedRef<'a, NodeStore<Meta>>;

/// Stores the nodes of the quadtree.
pub struct NodeStore<Meta> {
    inner: ConcurrentHashTable<QuadTreeNode<Meta>>,
}

unsafe impl<Meta: Sync> Sync for NodeStore<Meta> {}

impl<Meta: Default + Sync> NodeAccess<Meta> for NodeStore<Meta> {
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
    pub fn new(cap_log2: u32, threads_cnt: usize) -> Self {
        Self {
            inner: ConcurrentHashTable::new(cap_log2, threads_cnt),
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
        let (mut nw, mut ne) = (nw as u64, ne as u64);
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
        let (mut sw, mut se) = (sw as u64, se as u64);
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

    /// Single-threaded GC: marks all nodes reachable from `roots` (at level
    /// `size_log2`), then removes every unreachable node from the table's
    /// bucket chains and returns it to the free list.
    pub fn gc(&mut self, roots: &[Idx], size_log2: u32) {
        let mut live: AHashSet<Idx> = AHashSet::new();
        for &root in roots {
            self.collect_reachable(root, size_log2, &mut live);
        }
        // Reset computation state on surviving nodes. GC is called to
        // invalidate old cached results (e.g. step-size change), so FINISHED
        // status and cached Idxs are always stale here.
        // We intentionally leave `status_extra` and `extra` (StreamLife lane
        // data) untouched — they depend only on cell structure, which is
        // immutable for a given Idx.
        for &idx in &live {
            let n = self.get(idx);
            n.status.store(0, Ordering::Relaxed);
            n.cache.set_value(Idx::default());
        }
        self.inner.gc(|idx| !live.contains(&idx));
    }

    fn collect_reachable(&self, idx: Idx, size_log2: u32, live: &mut AHashSet<Idx>) {
        if !live.insert(idx) {
            return;
        }
        if size_log2 > LEAF_SIZE_LOG2 {
            let n = self.get(idx);
            for child in n.parts() {
                self.collect_reachable(child, size_log2 - 1, live);
            }
            // Also follow the cached result for FINISHED nodes. The result is
            // a structural node at level size_log2-1 that will likely be
            // looked up again in future computations, so keeping it alive
            // avoids re-allocating and re-inserting it.
            if n.status.load(Ordering::Relaxed) & status::FINISHED != 0 {
                self.collect_reachable(n.cache.get_value(), size_log2 - 1, live);
            }
        }
    }
}

impl<'a, Meta: Default + Sync> NodeStoreRef<'a, Meta> {
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

    pub fn exceeds_load_factor(&self) -> bool {
        self.base.exceeds_load_factor()
    }
}

impl<'a, Meta: Default + Sync> NodeAccess<Meta> for NodeStoreRef<'a, Meta> {
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
