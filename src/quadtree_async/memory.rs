use super::{
    node::{NodeIdx, QuadTreeNode},
    sharded_length::{LengthShard, ShardedLength},
};
use std::{cell::UnsafeCell, hint, mem, sync::atomic::{AtomicU8, Ordering}};

const MAX_LOAD_FACTOR: f64 = 0.75;

// Flag constants for the ConcurrentHashTable slot flags field.
// Bit 0 is type-specific (e.g., FLAG_LEAF for QuadTreeNode).
pub(super) const FLAG_USED: u8 = 1 << 1;
const FLAG_LOCKED: u8 = 1 << 2;
const FLAG_LEAF: u8 = 1 << 0;

/// Trait for types that can be stored as entries in a [`ConcurrentHashTable`].
///
/// Implementors must provide access to an [`AtomicU8`] flags field that the
/// hash table uses for per-slot locking and occupancy tracking.
pub(super) trait HashtableSlot: Default + Sync {
    fn flags(&self) -> &AtomicU8;
}

impl<Extra: Default + Sync> HashtableSlot for QuadTreeNode<Extra> {
    fn flags(&self) -> &AtomicU8 {
        &self.flags
    }
}

/// A concurrent open-addressing hashtable with linear probing.
///
/// Uses per-slot locking via atomic flags. The table never grows;
/// capacity is fixed at creation time.
pub(super) struct ConcurrentHashTable<E> {
    hashtable: Box<[UnsafeCell<E>]>,
    length: ShardedLength,
    length_limit: usize,
}

// SAFETY: Concurrent access is protected by per-slot atomic flags.
unsafe impl<E: Sync> Sync for ConcurrentHashTable<E> {}

impl<E: HashtableSlot> ConcurrentHashTable<E> {
    /// Create a new hash table with capacity `2^cap_log2`.
    pub(super) fn new(cap_log2: u32, threads_cnt: usize) -> Self {
        let max_cap_log2 = mem::size_of::<u32>() as u32 * 8;
        assert!(
            cap_log2 <= max_cap_log2,
            "Hashtables bigger than 2^{max_cap_log2} are not supported"
        );
        Self {
            hashtable: (0..1u64 << cap_log2)
                .map(|_| UnsafeCell::new(E::default()))
                .collect(),
            length: ShardedLength::new(threads_cnt),
            length_limit: (2f64.powi(cap_log2 as i32) * MAX_LOAD_FACTOR) as usize,
        }
    }

    /// Get a reference to the entry at the given index.
    pub(super) fn get(&self, idx: u32) -> &E {
        unsafe { &*self.hashtable.get_unchecked(idx as usize).get() }
    }

    /// Find an entry matching the given criteria; if not found, create one.
    ///
    /// ## Lock-free Optimization
    ///
    /// Uses optimistic lock-free reading for the common case (entry exists):
    /// 1. Read `flags` with Acquire ordering
    /// 2. If flags match `target_flags`, safely check key via `key_matches`
    /// 3. If match, return immediately without lock
    ///
    /// For the rare case (creating new entry):
    /// 1. Acquire slot lock via `flags`
    /// 2. Double-check entry doesn't exist
    /// 3. Initialize via `init`, then set flags with Release ordering
    pub(super) fn find_or_create(
        &self,
        hash: usize,
        target_flags: u8,
        key_matches: impl Fn(*const E) -> bool,
        init: impl FnOnce(*mut E),
    ) -> (u32, bool) {
        let mask = self.hashtable.len() - 1;
        let mut index = hash & mask;

        loop {
            let slot = unsafe { UnsafeCell::raw_get(self.hashtable.as_ptr().add(index)) };
            let flags = unsafe { (*slot).flags() };

            // STEP 1: Optimistic read WITHOUT lock
            // Read flags with Acquire ordering - this synchronizes with Release store in creation
            let mut current_flags = flags.load(Ordering::Acquire);
            if current_flags == target_flags
                && key_matches(slot as *const E)
            {
                return (index as u32, false);
            }

            // STEP 2: Acquire slot lock
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

            // STEP 3: Double-check under lock (another thread may have created the entry)
            if current_flags == target_flags
                && key_matches(slot as *const E)
            {
                flags.store(target_flags, Ordering::Release);
                return (index as u32, false);
            }

            // STEP 4: Slot is free - create entry
            if current_flags & FLAG_USED == 0 {
                // Write data fields first
                init(slot);

                // CRITICAL: Write flags with Release ordering!
                flags.store(target_flags, Ordering::Release);
                return (index as u32, true);
            }

            // STEP 5: Collision - move to next slot
            flags.store(current_flags, Ordering::Release);
            index = index.wrapping_add(1) & mask;
        }
    }

    /// Increment the global length counter (non-sharded).
    pub(super) fn increment_length(&self) {
        self.length.increment();
    }

    /// Get a per-thread length shard for efficient concurrent counting.
    pub(super) fn get_shard(&self, shard_idx: usize) -> LengthShard<'_> {
        self.length.get_shard(shard_idx)
    }

    pub(super) fn clear(&mut self) {
        self.hashtable.fill_with(UnsafeCell::default);
    }

    pub(super) fn bytes_total(&self) -> usize {
        self.hashtable.len() * std::mem::size_of::<E>()
    }

    pub(super) fn len(&self) -> usize {
        self.length.get()
    }

    pub(super) fn exceeds_load_factor(&self) -> bool {
        self.length.get_upper_bound() > self.length_limit
    }
}

// ---------------------------------------------------------------------------
// MemoryManager: wraps ConcurrentHashTable<QuadTreeNode<Extra>>
// ---------------------------------------------------------------------------

/// Stores the nodes of the quadtree.
pub(super) struct MemoryManager<Extra> {
    inner: ConcurrentHashTable<QuadTreeNode<Extra>>,
}

unsafe impl<Extra: Sync> Sync for MemoryManager<Extra> {}

impl<Extra: Default + Sync> MemoryManager<Extra> {
    /// Create a new memory manager with capacity of `1 << cap_log2`.
    pub(super) fn new(cap_log2: u32, threads_cnt: usize) -> Self {
        Self {
            inner: ConcurrentHashTable::new(cap_log2, threads_cnt),
        }
    }

    /// Get a const reference to the node at the given index.
    pub(super) fn get(&self, idx: NodeIdx) -> &QuadTreeNode<Extra> {
        self.inner.get(idx.0)
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
            self.inner.increment_length();
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
            self.inner.increment_length();
        }
        result
    }

    fn find_or_create_leaf_from_u64_inner(&self, value: u64) -> (NodeIdx, bool) {
        let rows = value.to_le_bytes();
        let nw = NodeIdx(u32::from_le_bytes(rows[0..4].try_into().unwrap()));
        let ne = NodeIdx(u32::from_le_bytes(rows[4..8].try_into().unwrap()));
        let (sw, se) = (NodeIdx::default(), NodeIdx::default());
        let hash = compute_hash(nw, ne, sw, se);
        let target_flags = FLAG_LEAF | FLAG_USED;
        let (idx, inserted) = self.inner.find_or_create(
            hash,
            target_flags,
            |slot| unsafe { ((*slot).nw, (*slot).ne, (*slot).sw, (*slot).se) == (nw, ne, sw, se) },
            |slot| unsafe {
                ((*slot).nw, (*slot).ne, (*slot).sw, (*slot).se) = (nw, ne, sw, se);
            },
        );
        (NodeIdx(idx), inserted)
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
            self.inner.increment_length();
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
        let hash = compute_hash(nw, ne, sw, se);
        let target_flags = FLAG_USED;
        let (idx, inserted) = self.inner.find_or_create(
            hash,
            target_flags,
            |slot| unsafe { ((*slot).nw, (*slot).ne, (*slot).sw, (*slot).se) == (nw, ne, sw, se) },
            |slot| unsafe {
                ((*slot).nw, (*slot).ne, (*slot).sw, (*slot).se) = (nw, ne, sw, se);
            },
        );
        (NodeIdx(idx), inserted)
    }

    /// Create a per-thread reference to this memory manager.
    pub(super) fn create_ref(&self, shard_idx: usize) -> MemoryManagerRef<'_, Extra> {
        MemoryManagerRef {
            base: self,
            length_shard: self.inner.get_shard(shard_idx),
        }
    }

    pub(super) fn clear(&mut self) {
        self.inner.clear();
    }

    pub(super) fn bytes_total(&self) -> usize {
        self.inner.bytes_total()
    }

    pub(super) fn len(&self) -> usize {
        self.inner.len()
    }

    pub(super) fn exceeds_load_factor(&self) -> bool {
        self.inner.exceeds_load_factor()
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
    length_shard: LengthShard<'a>,
}

impl<'a, Extra: Default + Sync> MemoryManagerRef<'a, Extra> {
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
            self.length_shard.increment();
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
            self.length_shard.increment();
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
            self.length_shard.increment();
        }
        result
    }

    pub(super) fn exceeds_load_factor(&self) -> bool {
        self.base.exceeds_load_factor()
    }
}
