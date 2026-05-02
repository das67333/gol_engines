//! # Concurrent chained hashtable with per-thread node chunks
//!
//! See `chained_hashtable_design.md` for the full design rationale.
//!
//! ## Layout
//!
//! - A fixed-size **bucket array** of `AtomicU32`. Each bucket holds the
//!   `Idx` of the head of its chain (or `NULL_IDX = 0` for empty).
//! - A fixed-size **chunks table** (`Box<[Chunk<E>]>`). Each `Chunk<E>`
//!   has an `AtomicPtr` to its node storage, lazily allocated on first
//!   claim. `chunks[0]` is reserved (its storage stays null) so that any
//!   `Idx` with `chunk_id == 0` is null.
//! - One **`ThreadState`** per shard, holding the thread's current chunk,
//!   bump-pointer offset within it, and a thread-local free-list head.
//! - A global `next_chunk_id: AtomicU32` bumped via `fetch_add` to claim
//!   new chunks.
//!
//! ## Idx encoding
//!
//! ```text
//! ┌────────────────────────┬────────────────────────┐
//! │       chunk_id         │       offset           │
//! │      32 - CHUNK_LOG2   │      CHUNK_LOG2        │
//! └────────────────────────┴────────────────────────┘
//! ```
//!
//! `Idx = 0` (chunk_id=0, offset=0) means null.
//!
//! ## Lock-free `find_or_create`
//!
//! Walk chain → if key matches, return that Idx. Otherwise allocate a new
//! slot from this thread's pool, initialize, set `next` to current head,
//! Release-CAS the bucket head. On CAS failure, walk only the *new*
//! portion of the chain looking for the same key (someone else may have
//! inserted it concurrently); if not found, update `next` to the new head
//! and retry the CAS.
//!
//! Under same-key contention, only the first thread does the CAS; all
//! others find their key on retry. No spinlock; no per-slot lock.

use super::{node::QuadTreeNode, sharded_statistics::*};
use std::{
    cell::UnsafeCell,
    hash::{Hash, Hasher},
    mem, ptr,
    sync::atomic::{AtomicPtr, AtomicU8, AtomicU32, Ordering},
};

/// Index into a [`ConcurrentHashTable`]. Encoded as `(chunk_id, offset)`;
/// see module-level docs.
pub(super) type Idx = u32;

/// The null Idx. Chunk 0 is reserved (its storage is never allocated), so
/// any encoded Idx with `chunk_id == 0` is null. `Idx::default()` is `0`.
pub(super) const NULL_IDX: Idx = 0;

/// Log2 of the per-chunk node count. 16 → 64 K nodes per chunk.
const CHUNK_LOG2: u32 = 16;
const CHUNK_SIZE: u32 = 1 << CHUNK_LOG2;
const OFFSET_MASK: u32 = CHUNK_SIZE - 1;

/// Bound on the number of `find_or_create_*` allocations a worker may issue
/// inside a single `process_task` invocation. The cancellation flag is read
/// only between tasks, so once a task starts it can claim up to this many
/// new slots before observing the flag. Used to size the safety margin
/// between [`ConcurrentHashTable::length_limit`] (cancellation threshold)
/// and the table's hard capacity.
///
/// 64 is a generous upper bound — measured worst-case is ~14
/// (`nine_children_disjoint` 9 + `four_children_overlapping` 4 + final result
/// 1).
pub(super) const MAX_ALLOCS_PER_TASK: usize = 64;

#[inline(always)]
fn chunk_id(idx: Idx) -> u32 {
    idx >> CHUNK_LOG2
}

#[inline(always)]
fn offset_in_chunk(idx: Idx) -> u32 {
    idx & OFFSET_MASK
}

#[inline(always)]
fn encode_idx(chunk_id: u32, offset: u32) -> Idx {
    assert!(offset < CHUNK_SIZE);
    (chunk_id << CHUNK_LOG2) | offset
}

/// Trait for types that can be stored in a [`ConcurrentHashTable`].
pub(super) trait HashtableSlot: Default + Sync {
    /// The chain pointer (also doubles as free-list link when freed).
    fn next(&self) -> &AtomicU32;
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

/// One chunk's storage. Lazy-allocated on first claim; `storage` is null
/// until then. The `Box<[UnsafeCell<E>]>` is reconstructed from the raw
/// pointer + known length (`CHUNK_SIZE`) in [`Chunk::release`] for drop.
struct Chunk<E> {
    storage: AtomicPtr<UnsafeCell<E>>,
}

impl<E> Chunk<E> {
    fn new() -> Self {
        Self {
            storage: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// Get a raw pointer to a slot inside this chunk. Caller must have
    /// observed (e.g. via Acquire load through bucket head) that the
    /// chunk has been claimed.
    #[inline(always)]
    fn slot(&self, offset: u32) -> *mut UnsafeCell<E> {
        let base = self.storage.load(Ordering::Acquire);
        assert!(!base.is_null(), "lookup of Idx in unclaimed chunk");
        unsafe { base.add(offset as usize) }
    }

    /// Drop the storage and reset to null. Single-threaded use only
    /// (called from `clear()` and `Drop`).
    fn release(&mut self) {
        let raw = *self.storage.get_mut();
        *self.storage.get_mut() = ptr::null_mut();
        if !raw.is_null() {
            unsafe {
                let slice = ptr::slice_from_raw_parts_mut(raw, CHUNK_SIZE as usize);
                drop(Box::from_raw(slice));
            }
        }
    }
}

impl<E> Drop for Chunk<E> {
    fn drop(&mut self) {
        self.release();
    }
}

/// Per-thread allocator state. Owner-only mutation; other threads only
/// read via `Idx` lookups (which go through the chunks table, not the
/// thread state).
struct ThreadState {
    /// Chunk this thread is currently allocating from. `0` = none yet.
    current_chunk_id: u32,
    /// Bump-pointer offset within `current_chunk_id`.
    next_offset_in_chunk: u32,
    /// Head of this thread's free list (or `NULL_IDX` if empty).
    free_list_head: Idx,
}

impl ThreadState {
    fn new() -> Self {
        Self {
            current_chunk_id: 0,
            next_offset_in_chunk: 0,
            free_list_head: NULL_IDX,
        }
    }

    fn reset(&mut self) {
        *self = Self::new();
    }
}

/// Concurrent chained hashtable backed by per-thread node chunks.
///
/// See module docs for the full design.
pub(super) struct ConcurrentHashTable<E> {
    /// Bucket array. Each entry is the head Idx of a chain.
    buckets: Box<[AtomicU32]>,
    /// Chunks table. `chunks[0]` is reserved as null; chunks[1..] are
    /// claimed lazily by threads via `next_chunk_id.fetch_add`.
    chunks: Box<[Chunk<E>]>,
    /// Bump pointer for chunk claims. Starts at 1 (chunk 0 reserved).
    next_chunk_id: AtomicU32,
    /// Per-thread allocator state (one entry per shard).
    thread_states: Box<[UnsafeCell<ThreadState>]>,
    /// Length tracking (existing sharded mechanism).
    length: ShardedLength,
    /// Cancellation threshold: when `len_upper_bound > length_limit`, callers
    /// stop fetching new tasks. Set below `capacity` by [`MAX_ALLOCS_PER_TASK`]
    /// × `threads_cnt` so that the post-cancel allocation burst can complete
    /// without exceeding `capacity` or exhausting the chunks table.
    length_limit: usize,
    /// Hard cap: maximum number of nodes the table can hold. Equal to
    /// `bucket_count` (load factor 1) when the chunks table can address that
    /// many; capped tighter at the boundary `cap_log2 ≈ 32` where the chunk
    /// table cannot host both the storage chunks and one partial chunk per
    /// thread without exceeding the 16-bit chunk-id space.
    capacity: usize,
}

// SAFETY:
// - `buckets`, `chunks`, `next_chunk_id`, `length` are all atomic / Sync.
// - `thread_states[i]` is mutated only by shard `i` (or single-threadedly
//   in `clear()`/`Drop`); other threads do not access `thread_states`.
// - `Chunk<E>::storage` is an `AtomicPtr` published with Release before
//   any Idx into the chunk can be observed by other threads.
unsafe impl<E: Sync> Sync for ConcurrentHashTable<E> {}

impl<E: HashtableSlot> ConcurrentHashTable<E> {
    /// Create a new table with `2^cap_log2` buckets and node capacity equal
    /// to `bucket_count` (load factor 1), capped by what the chunks table
    /// can address.
    ///
    /// ## Cancellation budget
    ///
    /// `length_limit = capacity − threads × MAX_ALLOCS_PER_TASK` is the
    /// soft cancellation threshold. A worker observes the threshold only
    /// between tasks; once inside `process_task` it can claim up to
    /// [`MAX_ALLOCS_PER_TASK`] new slots before re-checking. Reserving
    /// `threads × MAX_ALLOCS_PER_TASK` slots of headroom guarantees the
    /// post-cancel burst stays within `capacity`, so we never need to
    /// over-provision chunks beyond what's addressable.
    ///
    /// ## Chunks table sizing
    ///
    /// The table must address `capacity` nodes plus one partial chunk per
    /// thread (each thread can be mid-fill on its own chunk), plus the
    /// reserved chunk 0. The maximum chunk id is `2^(32 - CHUNK_LOG2)`
    /// (the `Idx = (chunk_id, offset)` encoding); when that limit binds
    /// (`cap_log2 ≈ 32`), `capacity` is reduced accordingly.
    ///
    /// `threads_cnt` is the number of shards (one `ThreadState` per shard).
    fn new(cap_log2: u32, threads_cnt: usize) -> Self {
        let max_cap_log2 = mem::size_of::<Idx>() as u32 * 8;
        assert!(
            cap_log2 <= max_cap_log2,
            "Hashtables bigger than 2^{max_cap_log2} are not supported"
        );
        let bucket_count = 1usize << cap_log2;

        // Hard ceiling from the `Idx` encoding: chunk id fits in
        // `32 - CHUNK_LOG2` bits, so there are `2^(32 - CHUNK_LOG2)` chunk
        // slots in total (chunk 0 reserved as the null sentinel).
        let chunk_id_count = 1usize << (mem::size_of::<Idx>() as u32 * 8 - CHUNK_LOG2);
        // Reserve one chunk per shard for partial-chunk in-flight allocations
        // (each thread can have its own current_chunk only partially filled).
        // Plus chunk 0 reserved.
        let max_storage_chunks = chunk_id_count
            .saturating_sub(1)
            .saturating_sub(threads_cnt);
        let max_storage_nodes = max_storage_chunks * CHUNK_SIZE as usize;

        // Load factor 1 capped by chunk-table addressability.
        let capacity = bucket_count.min(max_storage_nodes);

        // Cancellation threshold: leaves room for in-flight post-cancel
        // allocations.
        let safety_margin = threads_cnt.saturating_mul(MAX_ALLOCS_PER_TASK);
        let length_limit = capacity.saturating_sub(safety_margin);

        // Pre-allocate enough chunk slots to back `capacity` nodes plus per-
        // thread partial chunks plus the reserved chunk 0. Cap at the hard
        // ceiling.
        let needed_chunks = capacity
            .div_ceil(CHUNK_SIZE as usize)
            .saturating_add(threads_cnt)
            .saturating_add(1)
            .min(chunk_id_count);
        let chunks: Box<[Chunk<E>]> = (0..needed_chunks).map(|_| Chunk::new()).collect();

        let buckets: Box<[AtomicU32]> = (0..bucket_count).map(|_| AtomicU32::new(NULL_IDX)).collect();

        let thread_states: Box<[UnsafeCell<ThreadState>]> = (0..threads_cnt)
            .map(|_| UnsafeCell::new(ThreadState::new()))
            .collect();

        Self {
            buckets,
            chunks,
            // Skip chunk 0 (reserved as null sentinel).
            next_chunk_id: AtomicU32::new(1),
            thread_states,
            length: ShardedLength::new(threads_cnt),
            length_limit,
            capacity,
        }
    }

    /// Get a reference to the entry at the given `Idx`.
    ///
    /// # Panics (debug)
    /// If `idx == NULL_IDX` or its chunk is not yet claimed.
    fn get(&self, idx: Idx) -> &E {
        assert!(idx != NULL_IDX, "get(NULL_IDX)");
        let cid = chunk_id(idx);
        let off = offset_in_chunk(idx);
        let slot_ptr = self.chunks[cid as usize].slot(off);
        unsafe { &*(*slot_ptr).get() }
    }

    /// Mutable raw access for the inserting thread, before publication.
    /// SAFETY: caller guarantees no other thread can observe this slot
    /// (i.e. this slot has just been allocated and the publishing CAS
    /// has not yet run).
    fn get_uninit_mut(&self, idx: Idx) -> *mut E {
        let cid = chunk_id(idx);
        let off = offset_in_chunk(idx);
        let slot_ptr = self.chunks[cid as usize].slot(off);
        unsafe { (*slot_ptr).get() }
    }

    /// Find an entry matching `key_matches`; if not found, allocate a new
    /// slot, run `init` to populate the key fields, and publish into the
    /// chain via Release-CAS on the bucket head.
    ///
    /// Returns `(idx, was_inserted)`.
    ///
    /// `shard_idx` selects the per-thread allocator (and matters only if
    /// allocation occurs).
    fn find_or_create(
        &self,
        hash: usize,
        shard_idx: usize,
        key_matches: impl Fn(&E) -> bool,
        init: impl FnOnce(*mut E),
    ) -> (Idx, bool) {
        let bucket_mask = self.buckets.len() - 1;
        let bucket = hash & bucket_mask;

        // Phase 1: walk chain looking for an existing match.
        let mut head = self.buckets[bucket].load(Ordering::Acquire);
        let mut cur = head;
        while cur != NULL_IDX {
            let entry = self.get(cur);
            if key_matches(entry) {
                return (cur, false);
            }
            cur = entry.next().load(Ordering::Acquire);
        }

        // Phase 2: allocate from this thread's pool; populate fields.
        let new_idx = self.allocate(shard_idx);
        // SAFETY: the freshly-allocated slot is owned by this thread until
        // the publishing CAS in Phase 3.
        let new_ptr = self.get_uninit_mut(new_idx);
        unsafe {
            // Reset all fields to default state (handles free-list reuse
            // where the previous occupant left arbitrary contents).
            ptr::write(new_ptr, E::default());
            // Run caller-supplied initializer for the key fields.
            init(new_ptr);
            // Set the chain link.
            (*new_ptr).next().store(head, Ordering::Relaxed);
        }

        // Phase 3: publish via Release-CAS on bucket head.
        loop {
            match self.buckets[bucket].compare_exchange_weak(
                head,
                new_idx,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(_) => return (new_idx, true),
                Err(actual_head) => {
                    // Walk only the *new* portion of the chain (from
                    // actual_head down to old head) looking for our key
                    // (someone may have inserted it concurrently).
                    let mut cur = actual_head;
                    while cur != head {
                        let entry = self.get(cur);
                        if key_matches(entry) {
                            // Lost the race; recycle our slot.
                            self.deallocate(shard_idx, new_idx);
                            return (cur, false);
                        }
                        cur = entry.next().load(Ordering::Acquire);
                    }
                    head = actual_head;
                    unsafe {
                        (*new_ptr).next().store(head, Ordering::Relaxed);
                    }
                }
            }
        }
    }

    /// Allocate a fresh `Idx` from the given thread's pool. Prefers the
    /// free list; falls back to bumping within the current chunk;
    /// claims a new chunk if the current one is full.
    fn allocate(&self, shard_idx: usize) -> Idx {
        let ts = self.thread_state_mut(shard_idx);

        // Free list first.
        if ts.free_list_head != NULL_IDX {
            let idx = ts.free_list_head;
            // SAFETY: the freed slot's `next` field points to the next
            // free entry (set in `deallocate`).
            let entry = self.get(idx);
            ts.free_list_head = entry.next().load(Ordering::Relaxed);
            return idx;
        }

        // Bump within current chunk.
        if ts.current_chunk_id != 0 && ts.next_offset_in_chunk < CHUNK_SIZE {
            let off = ts.next_offset_in_chunk;
            ts.next_offset_in_chunk = off + 1;
            return encode_idx(ts.current_chunk_id, off);
        }

        // Claim a new chunk.
        self.claim_chunk(ts);
        let off = ts.next_offset_in_chunk;
        ts.next_offset_in_chunk = off + 1;
        encode_idx(ts.current_chunk_id, off)
    }

    fn claim_chunk(&self, ts: &mut ThreadState) {
        let id = self.next_chunk_id.fetch_add(1, Ordering::Relaxed);
        assert!(
            (id as usize) < self.chunks.len(),
            "chunks table exhausted (id={}, max={})",
            id,
            self.chunks.len()
        );
        // Allocate storage for this chunk.
        let storage: Box<[UnsafeCell<E>]> = (0..CHUNK_SIZE as usize)
            .map(|_| UnsafeCell::new(E::default()))
            .collect();
        let raw = Box::into_raw(storage) as *mut UnsafeCell<E>;
        // Publish: any subsequent observation of an Idx in this chunk
        // (via a Release-CAS on a bucket head) synchronizes with this
        // Release.
        self.chunks[id as usize].storage.store(raw, Ordering::Release);
        ts.current_chunk_id = id;
        ts.next_offset_in_chunk = 0;
    }

    fn deallocate(&self, shard_idx: usize, idx: Idx) {
        let ts = self.thread_state_mut(shard_idx);
        let entry = self.get(idx);
        entry.next().store(ts.free_list_head, Ordering::Relaxed);
        ts.free_list_head = idx;
    }

    /// SAFETY: caller must access only their own shard. We rely on
    /// the executor's per-thread sharding discipline.
    #[allow(clippy::mut_from_ref)]
    fn thread_state_mut(&self, shard_idx: usize) -> &mut ThreadState {
        unsafe { &mut *self.thread_states[shard_idx].get() }
    }

    fn increment_length(&self) {
        self.length.inc_global();
    }

    fn shard(&self, shard_idx: usize) -> LengthShard<'_> {
        self.length.shard(shard_idx)
    }

    /// Reset the table: clear buckets, drop all chunk storages, reset
    /// per-thread states, and reset the chunk-id counter. Single-threaded
    /// (called between updates).
    fn clear(&mut self) {
        for b in self.buckets.iter() {
            b.store(NULL_IDX, Ordering::Relaxed);
        }
        for chunk in self.chunks.iter_mut() {
            chunk.release();
        }
        self.next_chunk_id.store(1, Ordering::Relaxed);
        for ts in self.thread_states.iter_mut() {
            ts.get_mut().reset();
        }
        self.length.clear();
    }

    fn bytes_total(&self) -> usize {
        let next = self.next_chunk_id.load(Ordering::Relaxed) as usize;
        // Chunks 1..next have been claimed and have allocated storage.
        // Chunk 0 is reserved (no storage).
        let chunk_storage = next.saturating_sub(1) * CHUNK_SIZE as usize * mem::size_of::<E>();
        let chunks_table = self.chunks.len() * mem::size_of::<Chunk<E>>();
        let buckets = self.buckets.len() * mem::size_of::<AtomicU32>();
        let thread_states = self.thread_states.len() * mem::size_of::<UnsafeCell<ThreadState>>();
        chunk_storage + chunks_table + buckets + thread_states
    }

    fn len(&self) -> usize {
        self.length.len_exact()
    }

    /// Hard cap on the number of nodes this table can hold without
    /// exceeding the chunk-table addressability bound. Equals `bucket_count`
    /// (load factor 1) except at the `cap_log2 ≈ 32` boundary, where the
    /// 16-bit chunk-id space forces a tighter cap.
    fn capacity(&self) -> usize {
        self.capacity
    }

    fn exceeds_load_factor(&self) -> bool {
        self.length.len_upper_bound() > self.length_limit
    }

    /// Invoke `f` once per `Idx` whose backing storage has been allocated
    /// (i.e. every offset of every claimed chunk: chunk_id ∈ [1,
    /// next_chunk_id), offset ∈ [0, CHUNK_SIZE)).
    ///
    /// `0..capacity()` is **not** a valid Idx range — `Idx` is encoded
    /// `(chunk_id << CHUNK_LOG2) | offset`, so iteration must walk the
    /// chunk/offset axes explicitly. Some yielded Idxs may have status
    /// `NOT_STARTED` (slot was never published, was on a thread's free
    /// list, or sits past a chunk's high-water mark); callers must filter
    /// on the slot's own state.
    ///
    /// SAFETY: single-threaded use only — does not synchronize with
    /// concurrent `claim_chunk` / `allocate`. Intended for cancellation /
    /// GC paths after `thread::scope` has joined.
    fn for_each_idx(&self, mut f: impl FnMut(Idx)) {
        let next_id = self.next_chunk_id.load(Ordering::Relaxed);
        for cid in 1..next_id {
            for off in 0..CHUNK_SIZE {
                f(encode_idx(cid, off));
            }
        }
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

/// A per-thread reference to a store that uses local sharding for length
/// tracking *and* per-thread chunk allocation.
pub(super) struct ShardedRef<'a, S> {
    base: &'a S,
    shard_idx: usize,
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

    /// Find a leaf node with the given parts (4×4 grids as 16-bit integers).
    pub(super) fn find_or_create_leaf_from_parts(&self, nw: u16, ne: u16, sw: u16, se: u16) -> Idx {
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
    pub(super) fn find_or_create_leaf_from_u64(&self, value: u64) -> Idx {
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
    pub(super) fn find_or_create_node(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> Idx {
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

    pub(super) fn create_ref(&self, shard_idx: usize) -> NodeStoreRef<'_, Meta> {
        ShardedRef {
            base: self,
            shard_idx,
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

    /// See [`ConcurrentHashTable::for_each_idx`]. Single-threaded use only.
    pub(super) fn for_each_idx(&self, f: impl FnMut(Idx)) {
        self.inner.for_each_idx(f);
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
        let (result, inserted) =
            self.base
                .find_or_create_leaf_from_parts_inner(self.shard_idx, nw, ne, sw, se);
        if inserted {
            self.length_shard.increment();
        }
        result
    }

    pub(super) fn find_or_create_leaf_from_u64(&self, value: u64) -> Idx {
        let (result, inserted) = self
            .base
            .find_or_create_leaf_from_u64_inner(self.shard_idx, value);
        if inserted {
            self.length_shard.increment();
        }
        result
    }

    pub(super) fn find_or_create_node(&self, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> Idx {
        let (result, inserted) = self
            .base
            .find_or_create_node_inner(self.shard_idx, nw, ne, sw, se);
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
    /// Chain pointer (also free-list link when freed).
    pub(super) next: AtomicU32,
    status: AtomicU8,
}

impl Default for CacheEntry {
    fn default() -> Self {
        Self {
            key: (0, 0),
            payload: CacheField::default(),
            next: AtomicU32::new(NULL_IDX),
            status: AtomicU8::new(0),
        }
    }
}

// SAFETY: Concurrent access is protected by the status state machine
// (for `payload` and `status`) and by atomic chain operations on `next`.
unsafe impl Sync for CacheEntry {}

impl HashtableSlot for CacheEntry {
    fn next(&self) -> &AtomicU32 {
        &self.next
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
    fn entry_inner(&self, shard_idx: usize, key: (Idx, Idx)) -> (Idx, bool) {
        let hash = {
            let mut hasher = self.hasher.clone();
            key.hash(&mut hasher);
            hasher.finish() as usize
        };
        self.inner.find_or_create(
            hash,
            shard_idx,
            |slot| slot.key == key,
            |slot| unsafe {
                (*slot).key = key;
            },
        )
    }

    /// Find or create a cache entry. Uses the global (non-sharded) length counter.
    pub(super) fn entry(&self, key: (Idx, Idx)) -> Idx {
        let (idx, inserted) = self.entry_inner(0, key);
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
            shard_idx,
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

    /// See [`ConcurrentHashTable::for_each_idx`]. Single-threaded use only.
    pub(super) fn for_each_idx(&self, f: impl FnMut(Idx)) {
        self.inner.for_each_idx(f);
    }

    pub(super) fn exceeds_load_factor(&self) -> bool {
        self.inner.exceeds_load_factor()
    }
}

// -- BinodeCacheRef methods --

impl<'a> BinodeCacheRef<'a> {
    /// Find or create a cache entry. Uses the per-thread sharded length counter.
    pub(super) fn entry(&self, key: (Idx, Idx)) -> Idx {
        let (idx, inserted) = self.base.entry_inner(self.shard_idx, key);
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
