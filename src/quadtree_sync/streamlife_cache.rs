use super::NodeIdx;
use std::{
    cell::UnsafeCell,
    hash::{Hash, Hasher},
};

pub(super) struct StreamLifeCache {
    base: UnsafeCell<StreamLifeCacheRaw>,
}

unsafe impl Sync for StreamLifeCache {}

#[derive(Default)]
pub(super) struct CacheEntry {
    key: (NodeIdx, NodeIdx),
    pub(super) value: (NodeIdx, NodeIdx),
    is_used: bool,
}

impl StreamLifeCache {
    pub(super) fn with_capacity(cap_log2: u32) -> Self {
        Self {
            base: UnsafeCell::new(StreamLifeCacheRaw::with_capacity(cap_log2)),
        }
    }

    #[allow(clippy::mut_from_ref)]
    pub(super) fn entry(&self, key: (NodeIdx, NodeIdx)) -> (bool, *mut CacheEntry) {
        unsafe { (*self.base.get()).find_or_create_entry(key) }
    }

    pub(super) fn clear(&mut self) {
        self.base.get_mut().hashtable.fill_with(CacheEntry::default);
    }

    pub(super) fn bytes_total(&self) -> usize {
        unsafe { (*self.base.get()).bytes_total() }
    }

    pub(super) fn is_poisoned(&self) -> bool {
        unsafe { (*self.base.get()).poisoned }
    }
}

struct StreamLifeCacheRaw {
    hashtable: Vec<CacheEntry>,
    len: usize,
    poisoned: bool,
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
            len: 0,
            poisoned: false,
            hasher: ahash::AHasher::default(),
        }
    }

    unsafe fn find_or_create_entry(&mut self, key: (NodeIdx, NodeIdx)) -> (bool, *mut CacheEntry) {
        let hash = {
            let mut hasher = self.hasher.clone();
            (key.0 .0, key.1 .0).hash(&mut hasher);
            hasher.finish() as usize
        };
        let mask = self.hashtable.len() - 1;
        let mut index = hash & mask;

        let cached = loop {
            let c = unsafe { self.hashtable.get_unchecked_mut(index) };

            if c.key == key && c.is_used {
                break true;
            }

            if !c.is_used {
                c.key = key;
                c.is_used = true;

                self.len += 1;
                if self.len > self.hashtable.len() * 3 / 4 {
                    self.poisoned = true;
                }
                break false;
            }

            index = index.wrapping_add(1) & mask;
        };

        (cached, unsafe { self.hashtable.get_unchecked_mut(index) })
    }

    fn bytes_total(&self) -> usize {
        self.hashtable.capacity() * std::mem::size_of::<CacheEntry>()
    }
}
