use super::{ExecutionStatistics, NodeIdx};
use std::{
    cell::UnsafeCell,
    hash::{Hash, Hasher},
    hint::spin_loop,
    sync::atomic::{AtomicBool, AtomicU8, Ordering},
};

pub(super) struct StreamLifeCache {
    base: UnsafeCell<StreamLifeCacheRaw>,
}

unsafe impl Sync for StreamLifeCache {}

#[derive(Default)]
pub(super) struct CacheEntry {
    key: (NodeIdx, NodeIdx),
    pub(super) value: (NodeIdx, NodeIdx),
    pub(super) status: AtomicU8,
    is_used: bool,
    lock: AtomicBool,
}

impl StreamLifeCache {
    pub(super) fn with_capacity(cap_log2: u32) -> Self {
        Self {
            base: UnsafeCell::new(StreamLifeCacheRaw::with_capacity(cap_log2)),
        }
    }

    #[allow(clippy::mut_from_ref)]
    pub(super) fn entry(&self, key: (NodeIdx, NodeIdx)) -> *mut CacheEntry {
        unsafe { (*self.base.get()).find_or_create_entry(key) }
    }

    pub(super) fn clear(&mut self) {
        self.base.get_mut().hashtable.fill_with(CacheEntry::default);
    }

    pub(super) fn bytes_total(&self) -> usize {
        unsafe { (*self.base.get()).bytes_total() }
    }
}

struct StreamLifeCacheRaw {
    hashtable: Vec<CacheEntry>,
    hasher: ahash::AHasher,
}

impl StreamLifeCacheRaw {
    fn with_capacity(cap_log2: u32) -> Self {
        assert!(
            cap_log2 <= 32,
            "Hashtables bigger than 2^32 are not supported"
        );
        Self {
            hashtable: (0..1u64 << cap_log2)
                .map(|_| CacheEntry::default())
                .collect(),
            hasher: ahash::AHasher::default(),
        }
    }

    unsafe fn find_or_create_entry(&mut self, key: (NodeIdx, NodeIdx)) -> *mut CacheEntry {
        let hash = {
            let mut hasher = self.hasher.clone();
            (key.0 .0, key.1 .0).hash(&mut hasher);
            hasher.finish() as usize
        };
        let mask = self.hashtable.len() - 1;
        let mut index = hash & mask;

        loop {
            // First check if we can acquire the lock for this index
            let lock = &(*self.hashtable.as_mut_ptr().add(index)).lock;

            while lock
                .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_err()
            {
                while lock.load(Ordering::Relaxed) {
                    spin_loop();
                }
            }

            // Now safely get the mutable reference after acquiring the lock
            let c = self.hashtable.get_unchecked_mut(index);

            if c.key == key && c.is_used {
                lock.store(false, Ordering::Release);
                break;
            }

            if !c.is_used {
                c.key = key;
                c.value = (NodeIdx::default(), NodeIdx::default());
                c.is_used = true;

                ExecutionStatistics::on_insertion::<1>();
                lock.store(false, Ordering::Release);
                break;
            }

            lock.store(false, Ordering::Release);
            index = index.wrapping_add(1) & mask;
        }

        self.hashtable.get_unchecked_mut(index)
    }

    fn bytes_total(&self) -> usize {
        self.hashtable.capacity() * std::mem::size_of::<CacheEntry>()
    }
}
