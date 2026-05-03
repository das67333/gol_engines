use super::base::{CacheField, ConcurrentHashTable, HashtableSlot, Idx, NULL_IDX};
use super::node_store::ShardedRef;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU8, AtomicU32};

pub struct CacheEntry {
    key: (Idx, Idx),
    /// Dual-purpose field: computed binode result or processing data pointer.
    pub payload: CacheField<(Idx, Idx)>,
    /// Chain pointer (also free-list link when freed).
    pub next: AtomicU32,
    pub status: AtomicU8,
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
    pub fn key(&self) -> (Idx, Idx) {
        self.key
    }

    pub fn status(&self) -> &AtomicU8 {
        &self.status
    }
}

/// Caches results of StreamLife's `update_binode` operation.
pub struct BinodeCache {
    inner: ConcurrentHashTable<CacheEntry>,
    hasher: ahash::AHasher,
}

impl BinodeCache {
    pub fn new(cap_log2: u32, threads_cnt: usize) -> Self {
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
    pub fn entry(&self, key: (Idx, Idx)) -> Idx {
        let (idx, inserted) = self.entry_inner(0, key);
        if inserted {
            self.inner.increment_length();
        }
        idx
    }

    pub fn get(&self, idx: Idx) -> &CacheEntry {
        self.inner.get(idx)
    }

    pub fn create_ref(&self, shard_idx: usize) -> BinodeCacheRef<'_> {
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
}

/// Type alias for per-thread BinodeCache references.
pub type BinodeCacheRef<'a> = ShardedRef<'a, BinodeCache>;

impl<'a> BinodeCacheRef<'a> {
    /// Find or create a cache entry. Uses the per-thread sharded length counter.
    pub fn entry(&self, key: (Idx, Idx)) -> Idx {
        let (idx, inserted) = self.base.entry_inner(self.shard_idx, key);
        if inserted {
            self.length_shard.increment();
        }
        idx
    }

    pub fn get(&self, idx: Idx) -> &CacheEntry {
        self.base.get(idx)
    }

    pub fn exceeds_load_factor(&self) -> bool {
        self.base.exceeds_load_factor()
    }
}
