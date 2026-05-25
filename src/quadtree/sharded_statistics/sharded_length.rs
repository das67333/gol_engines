use crossbeam::utils::CachePadded;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct ShardedLength {
    global: AtomicUsize,
    shards: Box<[CachePadded<AtomicUsize>]>,
    max_underestimation: usize,
}

const FLUSH_THRESHOLD: usize = 256;

impl ShardedLength {
    pub fn new(shards_cnt: usize) -> Self {
        let shards = (0..shards_cnt)
            .map(|_| CachePadded::new(AtomicUsize::new(0)))
            .collect::<Vec<_>>();
        Self {
            global: AtomicUsize::new(0),
            shards: shards.into_boxed_slice(),
            max_underestimation: FLUSH_THRESHOLD * shards_cnt,
        }
    }

    pub fn inc_global(&self) {
        self.global.fetch_add(1, Ordering::Relaxed);
    }

    pub fn len_exact(&self) -> usize {
        let shards_sum_exact = self
            .shards
            .iter()
            .map(|shard| shard.load(Ordering::Relaxed))
            .sum::<usize>();

        self.global.load(Ordering::Relaxed) + shards_sum_exact
    }

    pub fn shard(&self, shard_idx: usize) -> LengthShard<'_> {
        LengthShard {
            local: &self.shards[shard_idx],
            global: &self.global,
        }
    }

    pub fn len_upper_bound(&self) -> usize {
        self.global.load(Ordering::Relaxed) + self.max_underestimation
    }

    /// Reset to a known count (zero all shards, set global to `n`).
    pub fn set(&mut self, n: usize) {
        self.global.store(n, Ordering::Relaxed);
        for shard in &self.shards {
            shard.store(0, Ordering::Relaxed);
        }
    }
}

pub struct LengthShard<'a> {
    local: &'a AtomicUsize,
    global: &'a AtomicUsize,
}

impl LengthShard<'_> {
    pub fn increment(&self) {
        let new_value = self.local.fetch_add(1, Ordering::Relaxed) + 1;
        if new_value == FLUSH_THRESHOLD {
            self.local.store(0, Ordering::Relaxed);
            self.global.fetch_add(FLUSH_THRESHOLD, Ordering::Relaxed);
        }
    }
}
