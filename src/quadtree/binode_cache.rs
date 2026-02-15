use super::{
    node_store::{ConcurrentHashTable, HashtableSlot, FLAG_USED},
    node::NodeIdx,
    sharded_length::LengthShard,
};
use std::{
    hash::{Hash, Hasher},
    sync::atomic::AtomicU8,
};

/// Union for the cache entry's data field: either the computed result or
/// a pointer to processing data during parallel execution.
///
/// The active variant is determined by the entry's `status` field:
/// - PROCESSING/PENDING: `ptr` is active (points to `BiProcessingData`)
/// - FINISHED: `value` is active (the computed result)
/// - NOT_STARTED: neither is meaningful
#[derive(Clone, Copy)]
pub(super) union CachePayload {
    pub value: (NodeIdx, NodeIdx),
    pub ptr: *mut u8,
}

impl Default for CachePayload {
    fn default() -> Self {
        CachePayload {
            value: (NodeIdx::default(), NodeIdx::default()),
        }
    }
}

pub(super) struct CacheEntry {
    key: (NodeIdx, NodeIdx),
    pub(super) payload: CachePayload,
    pub(super) status: AtomicU8,
    /// Slot flags for ConcurrentHashTable (IS_USED, IS_LOCKED, etc.)
    pub(super) flags: AtomicU8,
}

impl Default for CacheEntry {
    fn default() -> Self {
        Self {
            key: (NodeIdx::default(), NodeIdx::default()),
            payload: CachePayload::default(),
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
    pub(super) fn get_value(&self) -> (NodeIdx, NodeIdx) {
        unsafe { self.payload.value }
    }

    pub(super) fn set_value(&self, v: (NodeIdx, NodeIdx)) {
        unsafe {
            let p = &self.payload as *const CachePayload as *mut CachePayload;
            (*p).value = v;
        }
    }

    pub(super) fn get_ptr<T>(&self) -> *mut T {
        unsafe { self.payload.ptr as *mut T }
    }

    pub(super) fn set_ptr<T>(&self, ptr: *mut T) {
        unsafe {
            let p = &self.payload as *const CachePayload as *mut CachePayload;
            (*p).ptr = ptr as *mut u8;
        }
    }

    pub(super) fn key(&self) -> (NodeIdx, NodeIdx) {
        self.key
    }
}

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
    fn entry_inner(&self, key: (NodeIdx, NodeIdx)) -> (u32, bool) {
        let hash = {
            let mut hasher = self.hasher.clone();
            (key.0 .0, key.1 .0).hash(&mut hasher);
            hasher.finish() as usize
        };
        self.inner.find_or_create(
            hash,
            FLAG_USED,
            |slot| unsafe { (*slot).key == key },
            |slot| unsafe {
                (*slot).key = key;
                (*slot).payload = CachePayload::default();
                (*slot).status = AtomicU8::new(0);
            },
        )
    }

    /// Find or create a cache entry for the given binode key.
    /// Returns the index of the entry in the hash table.
    /// Uses the global (non-sharded) length counter.
    pub(super) fn entry(&self, key: (NodeIdx, NodeIdx)) -> u32 {
        let (idx, inserted) = self.entry_inner(key);
        if inserted {
            self.inner.increment_length();
        }
        idx
    }

    /// Get a reference to the cache entry at the given index.
    pub(super) fn get(&self, idx: u32) -> &CacheEntry {
        self.inner.get(idx)
    }

    /// Create a per-thread reference with sharded length counting.
    pub(super) fn create_ref(&self, shard_idx: usize) -> BinodeCacheRef<'_> {
        BinodeCacheRef {
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
}

/// A per-thread reference to the BinodeCache that uses local sharding for length tracking.
pub(super) struct BinodeCacheRef<'a> {
    base: &'a BinodeCache,
    length_shard: LengthShard<'a>,
}

impl<'a> BinodeCacheRef<'a> {
    /// Find or create a cache entry for the given binode key.
    /// Returns the index of the entry in the hash table.
    /// Uses the per-thread sharded length counter.
    pub(super) fn entry(&self, key: (NodeIdx, NodeIdx)) -> u32 {
        let (idx, inserted) = self.base.entry_inner(key);
        if inserted {
            self.length_shard.increment();
        }
        idx
    }

    /// Get a reference to the cache entry at the given index.
    pub(super) fn get(&self, idx: u32) -> &CacheEntry {
        self.base.get(idx)
    }
}
