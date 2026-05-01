use super::{node::QuadTreeNode, sharded_statistics::*, spin::Spinner};
use std::{
    cell::UnsafeCell,
    hash::{Hash, Hasher},
    mem, ptr,
    sync::atomic::{AtomicU8, Ordering},
};

/// Index into a [`ConcurrentHashTable`].
pub(super) type Idx = u32;

const MAX_LOAD_FACTOR: f64 = 0.75;

// Flag constants for slot flags field.
// Bit 0 is type-specific (e.g., FLAG_LEAF for QuadTreeNode).
const FLAG_USED: u8 = 1 << 1;
const FLAG_LOCKED: u8 = 1 << 2;
const FLAG_LEAF: u8 = 1 << 0;

/// Trait for types that can be stored as entries in a [`ConcurrentHashTable`].
///
/// Implementors must provide access to an [`AtomicU8`] flags field that the
/// hash table uses for per-slot locking and occupancy tracking.
pub(super) trait HashtableSlot: Default + Sync {
    fn flags(&self) -> &AtomicU8;
}

/// Union that stores either a type-erased pointer or an inline value.
union PtrOrValue<V: Copy> {
    ptr: *mut u8,
    value: V,
}

/// Dual-purpose cache field storing either processing data (pointer) or
/// a computed result (value). Thread-safe interior mutability via [`UnsafeCell`].
///
/// Used by both [`QuadTreeNode`] (caches `Idx` results) and
/// [`CacheEntry`] (caches `(Idx, Idx)` binode results).
///
/// Concurrent access is coordinated by the status state machine of the
/// surrounding node/entry (see the `quadtree::status` module docs):
/// - The pointer is installed by the owner during the `PROCESSING` init
///   barrier (no other thread can observe the slot at that point).
/// - While `PENDING` or `ACTIVE` is set, the pointed-to `ProcessingData`
///   is mutated by the owner (during `ACTIVE`, on fields that pushers
///   never touch) and by pushers (only the `dependents` list, under
///   `DEPS_LOCK`).
/// - The final value is written by the owner during the `PROCESSING`
///   finish barrier and is then immutable.
pub(super) struct CacheField<V: Copy>(UnsafeCell<PtrOrValue<V>>);

// SAFETY: Protected by the status state machine.
unsafe impl<V: Copy> Sync for CacheField<V> {}

impl<V: Copy> Default for CacheField<V> {
    fn default() -> Self {
        CacheField(UnsafeCell::new(PtrOrValue {
            ptr: ptr::null_mut(),
        }))
    }
}

impl<V: Copy> std::fmt::Debug for CacheField<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CacheField").finish()
    }
}

impl<V: Copy> CacheField<V> {
    pub(super) fn get_value(&self) -> V {
        unsafe { (*self.0.get()).value }
    }

    pub(super) fn set_value(&self, v: V) {
        unsafe { (*self.0.get()).value = v }
    }

    /// # Safety (interior mutability)
    /// The status state machine guarantees only one thread accesses this at a time.
    #[allow(clippy::mut_from_ref)]
    pub(super) fn get_ref<T>(&self) -> &mut T {
        unsafe { &mut *((*self.0.get()).ptr as *mut T) }
    }

    pub(super) fn set_ptr<T>(&self, ptr: *mut T) {
        unsafe { (*self.0.get()).ptr = ptr as *mut u8 }
    }
}

/// A concurrent open-addressing hashtable with linear probing.
///
/// Uses per-slot locking via atomic flags. The table never grows;
/// capacity is fixed at creation time.
struct ConcurrentHashTable<E> {
    hashtable: Box<[UnsafeCell<E>]>,
    length: ShardedLength,
    length_limit: usize,
}

// SAFETY: Concurrent access is protected by per-slot atomic flags.
unsafe impl<E: Sync> Sync for ConcurrentHashTable<E> {}

impl<E: HashtableSlot> ConcurrentHashTable<E> {
    /// Create a new hash table with capacity `2^cap_log2`.
    fn new(cap_log2: u32, threads_cnt: usize) -> Self {
        let max_cap_log2 = mem::size_of::<Idx>() as u32 * 8;
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
    fn get(&self, idx: Idx) -> &E {
        unsafe { &*self.hashtable.get_unchecked(idx as usize).get() }
    }

    /// Find an entry matching the given criteria; if not found, create one.
    ///
    /// Probing is fully lock-free: published (USED) slots have immutable bodies,
    /// so probers can read and compare keys without any per-slot lock. The slot
    /// lock is acquired only at the actual insertion site (an empty slot we
    /// claim via CAS). This eliminates the cascading-spinlock pathology where
    /// readers and probers were serializing through long collision chains.
    ///
    /// Invariant — once `FLAG_USED` is set, the entry's body (key fields) is
    /// final and never modified again. The only mutation is the
    /// `0 → LOCKED → USED` transition, performed under exclusive ownership of
    /// the lock by the thread that won the CAS.
    fn find_or_create(
        &self,
        hash: usize,
        is_leaf: bool,
        kind: MetricKind,
        key_matches: impl Fn(*const E) -> bool,
        init: impl FnOnce(*mut E),
    ) -> (Idx, bool) {
        let mask = self.hashtable.len() - 1;
        let mut index = hash & mask;
        let target_leaf_bit: u8 = if is_leaf { FLAG_LEAF } else { 0 };
        let final_flags: u8 = FLAG_USED | target_leaf_bit;

        loop {
            let slot = unsafe { UnsafeCell::raw_get(self.hashtable.as_ptr().add(index)) };
            let flags = unsafe { (*slot).flags() };

            let current_flags = flags.load(Ordering::Acquire);

            // Fast path: published slot. Body is immutable; key check is lock-free.
            if current_flags & FLAG_USED != 0 {
                if (current_flags & FLAG_LEAF) == target_leaf_bit
                    && key_matches(slot as *const E)
                {
                    return (index as Idx, false);
                }
                index = index.wrapping_add(1) & mask;
                continue;
            }

            // Slot is not yet published. If another thread is mid-insert
            // (LOCKED but not USED), wait for the in-progress insert to finish
            // so we can decide whether the resulting entry matches our key
            // (return), differs (skip), or never materializes (re-claim).
            if current_flags & FLAG_LOCKED != 0 {
                let mut spinner = Spinner::new();
                while flags.load(Ordering::Acquire) & FLAG_LOCKED != 0 {
                    spinner.spin();
                }
                record_metric(spinner.count(), kind);
                continue;
            }

            // Slot is genuinely empty (0). Try to claim it.
            if flags
                .compare_exchange_weak(0, FLAG_LOCKED, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                init(slot);
                flags.store(final_flags, Ordering::Release);
                return (index as Idx, true);
            }
            // Lost the race. Retry the same index; the next iteration will see
            // either LOCKED (wait) or USED (skip-or-match).
        }
    }

    fn increment_length(&self) {
        self.length.inc_global();
    }

    fn shard(&self, shard_idx: usize) -> LengthShard<'_> {
        self.length.shard(shard_idx)
    }

    fn clear(&mut self) {
        self.hashtable.fill_with(UnsafeCell::default);
        self.length.clear();
    }

    fn bytes_total(&self) -> usize {
        self.hashtable.len() * std::mem::size_of::<E>()
    }

    fn len(&self) -> usize {
        self.length.len_exact()
    }

    fn capacity(&self) -> usize {
        self.hashtable.len()
    }

    fn exceeds_load_factor(&self) -> bool {
        self.length.len_upper_bound() > self.length_limit
    }
}

/// Shared interface for accessing nodes.
pub(super) trait NodeAccess<Meta: Default + Sync> {
    fn get(&self, idx: Idx) -> &QuadTreeNode<Meta>;
    fn find_or_create_node(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> Idx;
    fn find_or_create_leaf_from_u64(&self, value: u64) -> Idx;
    fn find_or_create_leaf_from_parts(&self, nw: u16, ne: u16, sw: u16, se: u16) -> Idx;
}

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

/// A per-thread reference to a store that uses local sharding for length tracking.
pub(super) struct ShardedRef<'a, S> {
    base: &'a S,
    length_shard: LengthShard<'a>,
}

/// Type alias for per-thread NodeStore references.
pub(super) type NodeStoreRef<'a, Meta> = ShardedRef<'a, NodeStore<Meta>>;

/// Type alias for per-thread BinodeCache references.
pub(super) type BinodeCacheRef<'a> = ShardedRef<'a, BinodeCache>;

/// Stores the nodes of the quadtree.
pub(super) struct NodeStore<Meta> {
    inner: ConcurrentHashTable<QuadTreeNode<Meta>>,
}

unsafe impl<Meta: Sync> Sync for NodeStore<Meta> {}

impl<Meta: Default + Sync> NodeStore<Meta> {
    pub(super) fn new(cap_log2: u32, threads_cnt: usize) -> Self {
        Self {
            inner: ConcurrentHashTable::new(cap_log2, threads_cnt),
        }
    }

    pub(super) fn get(&self, idx: Idx) -> &QuadTreeNode<Meta> {
        self.inner.get(idx)
    }

    /// Find a leaf node with the given parts (4x4 grids as 16-bit integers).
    pub(super) fn find_or_create_leaf_from_parts(&self, nw: u16, ne: u16, sw: u16, se: u16) -> Idx {
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

        self.find_or_create_leaf_from_u64_inner(cells)
    }

    /// Find a leaf node with the given cells (8x8 grid as 64-bit integer).
    pub(super) fn find_or_create_leaf_from_u64(&self, value: u64) -> Idx {
        let (result, inserted) = self.find_or_create_leaf_from_u64_inner(value);
        if inserted {
            self.inner.increment_length();
        }
        result
    }

    fn find_or_create_leaf_from_u64_inner(&self, value: u64) -> (Idx, bool) {
        let rows = value.to_le_bytes();
        let nw = u32::from_le_bytes(rows[0..4].try_into().unwrap());
        let ne = u32::from_le_bytes(rows[4..8].try_into().unwrap());
        let (sw, se) = (0, 0);
        let hash = compute_hash(nw, ne, sw, se);
        self.inner.find_or_create(
            hash,
            true,
            MetricKind::NodeStoreLock,
            |slot| unsafe { ((*slot).nw, (*slot).ne, (*slot).sw, (*slot).se) == (nw, ne, sw, se) },
            |slot| unsafe {
                ((*slot).nw, (*slot).ne, (*slot).sw, (*slot).se) = (nw, ne, sw, se);
            },
        )
    }

    /// Find a node with the given children. If not found, it is created.
    pub(super) fn find_or_create_node(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> Idx {
        let (result, inserted) = self.find_or_create_node_inner(nw, ne, sw, se);
        if inserted {
            self.inner.increment_length();
        }
        result
    }

    fn find_or_create_node_inner(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> (Idx, bool) {
        let hash = compute_hash(nw, ne, sw, se);
        self.inner.find_or_create(
            hash,
            false,
            MetricKind::NodeStoreLock,
            |slot| unsafe { ((*slot).nw, (*slot).ne, (*slot).sw, (*slot).se) == (nw, ne, sw, se) },
            |slot| unsafe {
                ((*slot).nw, (*slot).ne, (*slot).sw, (*slot).se) = (nw, ne, sw, se);
            },
        )
    }

    pub(super) fn create_ref(&self, shard_idx: usize) -> NodeStoreRef<'_, Meta> {
        ShardedRef {
            base: self,
            length_shard: self.inner.shard(shard_idx),
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

    pub(super) fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    pub(super) fn exceeds_load_factor(&self) -> bool {
        self.inner.exceeds_load_factor()
    }
}

/// Hash function for node hashtable lookup (polynomial hash with mixing).
fn compute_hash(nw: Idx, ne: Idx, sw: Idx, se: Idx) -> usize {
    let h = 0u32
        .wrapping_add(nw.wrapping_mul(5))
        .wrapping_add(ne.wrapping_mul(17))
        .wrapping_add(sw.wrapping_mul(257))
        .wrapping_add(se.wrapping_mul(65537));
    h.wrapping_add(h >> 11) as usize
}

impl<'a, Meta: Default + Sync> NodeStoreRef<'a, Meta> {
    pub(super) fn get(&self, idx: Idx) -> &QuadTreeNode<Meta> {
        self.base.get(idx)
    }

    pub(super) fn find_or_create_leaf_from_parts(&self, nw: u16, ne: u16, sw: u16, se: u16) -> Idx {
        let (result, inserted) = self
            .base
            .find_or_create_leaf_from_parts_inner(nw, ne, sw, se);
        if inserted {
            self.length_shard.increment();
        }
        result
    }

    pub(super) fn find_or_create_leaf_from_u64(&self, value: u64) -> Idx {
        let (result, inserted) = self.base.find_or_create_leaf_from_u64_inner(value);
        if inserted {
            self.length_shard.increment();
        }
        result
    }

    pub(super) fn find_or_create_node(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> Idx {
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

pub(super) struct CacheEntry {
    key: (Idx, Idx),
    /// Dual-purpose field: computed binode result or processing data pointer.
    pub(super) payload: CacheField<(Idx, Idx)>,
    status: AtomicU8,
    /// Slot flags for ConcurrentHashTable (IS_USED, IS_LOCKED, etc.)
    flags: AtomicU8,
}

impl Default for CacheEntry {
    fn default() -> Self {
        Self {
            key: (0, 0),
            payload: CacheField::default(),
            status: AtomicU8::new(0),
            flags: AtomicU8::new(0),
        }
    }
}

// SAFETY: Concurrent access is protected by the status state machine
// and the per-slot flags in ConcurrentHashTable.
unsafe impl Sync for CacheEntry {}

impl HashtableSlot for CacheEntry {
    fn flags(&self) -> &AtomicU8 {
        &self.flags
    }
}

impl CacheEntry {
    pub(super) fn key(&self) -> (Idx, Idx) {
        self.key
    }

    pub(super) fn status(&self) -> &AtomicU8 {
        &self.status
    }
}

/// Caches results of StreamLife's `update_binode` operation.
pub(super) struct BinodeCache {
    inner: ConcurrentHashTable<CacheEntry>,
    hasher: ahash::AHasher,
}

impl BinodeCache {
    pub(super) fn new(cap_log2: u32, threads_cnt: usize) -> Self {
        Self {
            inner: ConcurrentHashTable::new(cap_log2, threads_cnt),
            hasher: ahash::AHasher::default(),
        }
    }

    /// Find or create a cache entry for the given binode key.
    /// Returns `(index, was_inserted)`.
    fn entry_inner(&self, key: (Idx, Idx)) -> (Idx, bool) {
        let hash = {
            let mut hasher = self.hasher.clone();
            key.hash(&mut hasher);
            hasher.finish() as usize
        };
        self.inner.find_or_create(
            hash,
            false,
            MetricKind::BinodeCacheLock,
            |slot| unsafe { (*slot).key == key },
            |slot| unsafe {
                (*slot).key = key;
                (*slot).payload = CacheField::default();
                (*slot).status = AtomicU8::new(0);
            },
        )
    }

    /// Find or create a cache entry. Uses the global (non-sharded) length counter.
    pub(super) fn entry(&self, key: (Idx, Idx)) -> Idx {
        let (idx, inserted) = self.entry_inner(key);
        if inserted {
            self.inner.increment_length();
        }
        idx
    }

    pub(super) fn get(&self, idx: Idx) -> &CacheEntry {
        self.inner.get(idx)
    }

    pub(super) fn create_ref(&self, shard_idx: usize) -> BinodeCacheRef<'_> {
        ShardedRef {
            base: self,
            length_shard: self.inner.shard(shard_idx),
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

    pub(super) fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    pub(super) fn exceeds_load_factor(&self) -> bool {
        self.inner.exceeds_load_factor()
    }
}

// -- BinodeCacheRef methods --

impl<'a> BinodeCacheRef<'a> {
    /// Find or create a cache entry. Uses the per-thread sharded length counter.
    pub(super) fn entry(&self, key: (Idx, Idx)) -> Idx {
        let (idx, inserted) = self.base.entry_inner(key);
        if inserted {
            self.length_shard.increment();
        }
        idx
    }

    pub(super) fn get(&self, idx: Idx) -> &CacheEntry {
        self.base.get(idx)
    }

    pub(super) fn exceeds_load_factor(&self) -> bool {
        self.base.exceeds_load_factor()
    }
}
