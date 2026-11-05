use super::base::{CacheField, ConcurrentHashTable, HashtableSlot, Idx, NULL_IDX};
use super::node_store::{ShardedRef, NodeStore};
use super::super::{parallel_executors::GcSweepExecutor, status};
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU8, AtomicU32, Ordering};

pub struct CacheEntry {
    key: (Idx, Idx),
    /// Dual-purpose field: computed binode result or processing data pointer.
    payload: CacheField<(Idx, Idx)>,
    /// Chain pointer (also free-list link when freed).
    next: AtomicU32,
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
    pub fn key(&self) -> (Idx, Idx) {
        self.key
    }

    pub fn payload(&self) -> &CacheField<(Idx, Idx)> {
        &self.payload
    }

    pub fn status(&self) -> &AtomicU8 {
        &self.status
    }
}

/// Caches results of `StreamLife`'s `update_binode` operation.
pub struct BinodeCache {
    inner: ConcurrentHashTable<CacheEntry>,
    hasher: ahash::AHasher,
}

impl BinodeCache {
    pub fn new(cap_log2: u32, entry_capacity: usize, threads_cnt: usize) -> Self {
        Self {
            inner: ConcurrentHashTable::new(cap_log2, entry_capacity, threads_cnt),
            hasher: ahash::AHasher::default(),
        }
    }

    fn hash(&self, key: (Idx, Idx)) -> usize {
        let mut hasher = self.hasher.clone();
        key.hash(&mut hasher);
        hasher.finish() as usize
    }

    pub fn find(&self, key: (Idx, Idx)) -> Option<Idx> {
        self.inner.find(self.hash(key), |slot| slot.key == key)
    }

    /// Find or create a cache entry for the given binode key.
    /// Returns `(index, was_inserted)`.
    fn entry_inner(&self, shard_idx: usize, key: (Idx, Idx)) -> (Idx, bool) {
        self.inner.find_or_create(
            self.hash(key),
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

    /// Keep rooted pending work and finished pairs whose keys and results survive node GC.
    /// Workers have joined; run after marking and before recycling node indices.
    pub fn retain_marked<Meta: Default + Sync>(&mut self, nodes: &NodeStore<Meta>) {
        GcSweepExecutor::new(&mut self.inner).run(|entry| {
            let state = entry.status().load(Ordering::Relaxed);
            if state & status::PENDING != 0 {
                assert_ne!(state & status::GC_MARK, 0, "pending pair was not rooted");
                entry.status().store(status::PENDING, Ordering::Relaxed);
                return false;
            }
            if state != status::FINISHED {
                return true;
            }
            let (a, b) = entry.key();
            let (x, y) = entry.payload().get_value();
            ![a, b, x, y].into_iter().all(|idx| nodes.get(idx).status.load(Ordering::Relaxed) & status::GC_MARK != 0)
        });
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

/// Type alias for per-thread `BinodeCache` references.
pub type BinodeCacheRef<'a> = ShardedRef<'a, BinodeCache>;

impl BinodeCacheRef<'_> {
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
