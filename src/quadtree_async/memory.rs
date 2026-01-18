use super::node::{NodeIdx, QuadTreeNode};
use crossbeam::utils::CachePadded;
use std::{
    cell::UnsafeCell,
    hint, mem,
    sync::atomic::{AtomicUsize, Ordering},
};

/// Stores the nodes of the quadtree.
pub(super) struct MemoryManager<Extra> {
    hashtable: Box<[UnsafeCell<QuadTreeNode<Extra>>]>,
    length: ShardedLength,
}

unsafe impl<Extra: Sync> Sync for MemoryManager<Extra> {}

impl<Extra: Default> MemoryManager<Extra> {
    /// Create a new memory manager with capacity of `1 << cap_log2`.
    pub(super) fn new(cap_log2: u32, threads_cnt: usize) -> Self {
        let max_cap_log2 = mem::size_of::<NodeIdx>() as u32 * 8;
        assert!(
            cap_log2 <= max_cap_log2,
            "Hashtables bigger than 2^{max_cap_log2} are not supported"
        );
        Self {
            hashtable: (0..1u64 << cap_log2)
                .map(|_| UnsafeCell::new(QuadTreeNode::default()))
                .collect(),
            length: ShardedLength::new(threads_cnt),
        }
    }

    /// Get a const reference to the node at the given index.
    pub(super) fn get(&self, idx: NodeIdx) -> &QuadTreeNode<Extra> {
        unsafe { &*self.hashtable.get_unchecked(idx.0 as usize).get() }
    }

    /// Find a leaf node with the given parts.
    /// If the node is not found, it is created.
    ///
    /// `nw`, `ne`, `sw`, `se` represent 4x4 grids stored as 16-bit integers.
    /// The bits are packed in row-major order.
    pub(super) fn find_or_create_leaf_from_parts(
        &self,
        nw: u16,
        ne: u16,
        sw: u16,
        se: u16,
    ) -> NodeIdx {
        let (result, inserted) = self.find_or_create_leaf_from_parts_inner(nw, ne, sw, se);
        if inserted {
            self.length.increment_global();
        }
        result
    }

    fn find_or_create_leaf_from_parts_inner(
        &self,
        nw: u16,
        ne: u16,
        sw: u16,
        se: u16,
    ) -> (NodeIdx, bool) {
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

        self.find_or_create_leaf_from_u64_inner(cells)
    }

    /// Find a leaf node with the given cells.
    /// If the node is not found, it is created.
    ///
    /// `value` represents 8x8 grid stored as 64-bit integer.
    /// The bits are packed in row-major order.
    pub(super) fn find_or_create_leaf_from_u64(&self, value: u64) -> NodeIdx {
        let (result, inserted) = self.find_or_create_leaf_from_u64_inner(value);
        if inserted {
            self.length.increment_global();
        }
        result
    }

    fn find_or_create_leaf_from_u64_inner(&self, value: u64) -> (NodeIdx, bool) {
        let rows = value.to_le_bytes();
        let nw = NodeIdx(u32::from_le_bytes(rows[0..4].try_into().unwrap()));
        let ne = NodeIdx(u32::from_le_bytes(rows[4..8].try_into().unwrap()));
        let (sw, se) = (NodeIdx::default(), NodeIdx::default());
        self.find_or_create_generic::<true>(nw, ne, sw, se, compute_hash(nw, ne, sw, se))
    }

    /// Find a node with the given parts.
    /// If the node is not found, it is created.
    pub(super) fn find_or_create_node(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
    ) -> NodeIdx {
        let (result, inserted) = self.find_or_create_node_inner(nw, ne, sw, se);
        if inserted {
            self.length.increment_global();
        }
        result
    }

    fn find_or_create_node_inner(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
    ) -> (NodeIdx, bool) {
        self.find_or_create_generic::<false>(nw, ne, sw, se, compute_hash(nw, ne, sw, se))
    }

    /// Create a per-thread reference to this memory manager.
    pub(super) fn create_ref(&self, thread_idx: usize) -> MemoryManagerRef<'_, Extra> {
        MemoryManagerRef::new(self, thread_idx)
    }

    pub(super) fn clear(&mut self) {
        self.hashtable.fill_with(UnsafeCell::default);
    }

    pub(super) fn bytes_total(&self) -> usize {
        self.hashtable.len() * std::mem::size_of::<QuadTreeNode<Extra>>()
    }

    pub(super) fn len(&self) -> usize {
        self.length.get_exact()
    }

    /// Find an item in hashtable; if it is not present, it is created and its index is returned.
    ///
    /// ## Lock-free Optimization
    ///
    /// Uses optimistic lock-free reading for the common case (node exists):
    /// 1. Read `flags` with Acquire ordering
    /// 2. If flags match, safely read nw,ne,sw,se
    /// 3. If all fields match, return immediately without lock
    ///
    /// For the rare case (creating new node):
    /// 1. Acquire slot lock via `flags`
    /// 2. Double-check node doesn't exist
    /// 3. Write data fields, then set flags with Release ordering
    fn find_or_create_generic<const IS_LEAF: bool>(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        hash: usize,
    ) -> (NodeIdx, bool) {
        const FLAG_LEAF: u8 = 1 << 0;
        const FLAG_USED: u8 = 1 << 1;
        const FLAG_LOCKED: u8 = 1 << 2;

        let mask = self.hashtable.len() - 1;
        let mut index = hash & mask;
        let target_flags = (FLAG_LEAF * IS_LEAF as u8) | FLAG_USED;

        loop {
            let n = unsafe { UnsafeCell::raw_get(self.hashtable.as_ptr().add(index)) };
            let flags = unsafe { &(*n).flags };

            // STEP 1: Optimistic read WITHOUT lock
            // Read flags with Acquire ordering - this synchronizes with Release store in creation
            let mut current_flags = flags.load(Ordering::Acquire);
            if current_flags == target_flags
                && unsafe { ((*n).nw, (*n).ne, (*n).sw, (*n).se) == (nw, ne, sw, se) }
            {
                return (NodeIdx(index as u32), false);
            }

            // STEP 2: Not found optimistically - acquire slot lock
            loop {
                while current_flags & FLAG_LOCKED != 0 {
                    current_flags = flags.load(Ordering::Relaxed);
                    hint::spin_loop();
                }
                match flags.compare_exchange_weak(
                    current_flags,
                    current_flags | FLAG_LOCKED,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(value) => current_flags = value,
                }
            }

            // STEP 3: Double-check under lock (another thread may have created the node)
            if current_flags == target_flags
                && unsafe { ((*n).nw, (*n).ne, (*n).sw, (*n).se) == (nw, ne, sw, se) }
            {
                flags.store(target_flags, Ordering::Release);
                return (NodeIdx(index as u32), false);
            }

            // STEP 4: Slot is free - create node
            if !current_flags & FLAG_USED != 0 {
                // Write data fields first
                unsafe {
                    ((*n).nw, (*n).ne, (*n).sw, (*n).se) = (nw, ne, sw, se);
                }

                // CRITICAL: Write flags with Release ordering!
                flags.store(target_flags, Ordering::Release);

                // self.length.increment_local(thread_idx);
                return (NodeIdx(index as u32), true);
            }

            // STEP 5: Collision - move to next slot
            flags.store(current_flags, Ordering::Release);
            index = index.wrapping_add(1) & mask;
        }
    }
}

/// Hash function for hashtable lookup (polynomial hash with mixing).
fn compute_hash(nw: NodeIdx, ne: NodeIdx, sw: NodeIdx, se: NodeIdx) -> usize {
    let h = 0u32
        .wrapping_add((nw.0).wrapping_mul(5))
        .wrapping_add((ne.0).wrapping_mul(17))
        .wrapping_add((sw.0).wrapping_mul(257))
        .wrapping_add((se.0).wrapping_mul(65537));
    h.wrapping_add(h >> 11) as usize
}

/// A per-thread reference to the memory manager that uses local sharding for length tracking.
pub(super) struct MemoryManagerRef<'a, Extra> {
    base: &'a MemoryManager<Extra>,
    thread_idx: usize,
}

impl<'a, Extra: Default> MemoryManagerRef<'a, Extra> {
    pub(super) fn new(base: &'a MemoryManager<Extra>, thread_idx: usize) -> Self {
        Self { base, thread_idx }
    }

    /// Get a const reference to the node at the given index.
    pub(super) fn get(&self, idx: NodeIdx) -> &QuadTreeNode<Extra> {
        self.base.get(idx)
    }

    /// Find a leaf node with the given parts.
    /// If the node is not found, it is created.
    ///
    /// `nw`, `ne`, `sw`, `se` represent 4x4 grids stored as 16-bit integers.
    /// The bits are packed in row-major order.
    pub(super) fn find_or_create_leaf_from_parts(
        &self,
        nw: u16,
        ne: u16,
        sw: u16,
        se: u16,
    ) -> NodeIdx {
        let (result, inserted) = self
            .base
            .find_or_create_leaf_from_parts_inner(nw, ne, sw, se);
        if inserted {
            self.base.length.increment_local(self.thread_idx);
        }
        result
    }

    /// Find a leaf node with the given cells.
    /// If the node is not found, it is created.
    ///
    /// `value` represents 8x8 grid stored as 64-bit integer.
    /// The bits are packed in row-major order.
    pub(super) fn find_or_create_leaf_from_u64(&self, value: u64) -> NodeIdx {
        let (result, inserted) = self.base.find_or_create_leaf_from_u64_inner(value);
        if inserted {
            self.base.length.increment_local(self.thread_idx);
        }
        result
    }

    /// Find a node with the given parts.
    /// If the node is not found, it is created.
    pub(super) fn find_or_create_node(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
    ) -> NodeIdx {
        let (result, inserted) = self.base.find_or_create_node_inner(nw, ne, sw, se);
        if inserted {
            self.base.length.increment_local(self.thread_idx);
        }
        result
    }
}

struct ShardedLength {
    global: AtomicUsize,
    shards: Box<[CachePadded<AtomicUsize>]>,
    max_inaccuracy: usize,
}

impl ShardedLength {
    // must be even
    const FLUSH_THRESHOLD: usize = 256;

    fn new(shards_cnt: usize) -> Self {
        let shards = (0..shards_cnt)
            .map(|_| CachePadded::new(AtomicUsize::new(0)))
            .collect::<Vec<_>>();
        Self {
            global: AtomicUsize::new(0),
            shards: shards.into_boxed_slice(),
            max_inaccuracy: Self::FLUSH_THRESHOLD / 2 * shards_cnt,
        }
    }

    fn increment_global(&self) {
        self.global.fetch_add(1, Ordering::Relaxed);
    }

    fn increment_local(&self, thread_idx: usize) {
        let local = &self.shards[thread_idx];
        if local.fetch_add(1, Ordering::Relaxed) + 1 == Self::FLUSH_THRESHOLD {
            local.store(0, Ordering::Relaxed);
            self.global
                .fetch_add(Self::FLUSH_THRESHOLD, Ordering::Relaxed);
        }
    }

    fn get_approx(&self) -> usize {
        let shards_sum_approx = self.max_inaccuracy;
        self.global.load(Ordering::Relaxed) + shards_sum_approx
    }

    fn get_exact(&self) -> usize {
        let shards_sum_exact = self
            .shards
            .iter()
            .map(|shard| shard.load(Ordering::Relaxed))
            .sum::<usize>();

        self.global.load(Ordering::Relaxed) + shards_sum_exact
    }

    /// Returns the maximum possible error from the true value.
    fn max_error(&self) -> usize {
        self.max_inaccuracy
    }
}
