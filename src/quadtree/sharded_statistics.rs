use crossbeam::{deque::Steal, utils::CachePadded};
use std::sync::atomic::{AtomicUsize, Ordering};

pub(super) struct ShardedLength {
    global: AtomicUsize,
    shards: Box<[CachePadded<AtomicUsize>]>,
    max_underestimation: usize,
}

const FLUSH_THRESHOLD: usize = 256;

impl ShardedLength {
    pub(super) fn new(shards_cnt: usize) -> Self {
        let shards = (0..shards_cnt)
            .map(|_| CachePadded::new(AtomicUsize::new(0)))
            .collect::<Vec<_>>();
        Self {
            global: AtomicUsize::new(0),
            shards: shards.into_boxed_slice(),
            max_underestimation: FLUSH_THRESHOLD * shards_cnt,
        }
    }

    pub(super) fn increment(&self) {
        self.global.fetch_add(1, Ordering::Relaxed);
    }

    pub(super) fn get(&self) -> usize {
        let shards_sum_exact = self
            .shards
            .iter()
            .map(|shard| shard.load(Ordering::Relaxed))
            .sum::<usize>();

        self.global.load(Ordering::Relaxed) + shards_sum_exact
    }

    pub(super) fn get_shard(&self, shard_idx: usize) -> LengthShard<'_> {
        LengthShard {
            local: &self.shards[shard_idx],
            global: &self.global,
        }
    }

    pub(super) fn get_upper_bound(&self) -> usize {
        self.global.load(Ordering::Relaxed) + self.max_underestimation
    }
}

pub(super) struct LengthShard<'a> {
    local: &'a AtomicUsize,
    global: &'a AtomicUsize,
}

impl<'a> LengthShard<'a> {
    pub(super) fn increment(&self) {
        let new_value = self.local.fetch_add(1, Ordering::Relaxed) + 1;
        if new_value == FLUSH_THRESHOLD {
            self.local.store(0, Ordering::Relaxed);
            self.global.fetch_add(FLUSH_THRESHOLD, Ordering::Relaxed);
        }
    }
}

// static STEAL_ATTEMPTS_SUCCESS: AtomicU64 = AtomicU64::new(0);
// static STEAL_ATTEMPTS_EMPTY: AtomicU64 = AtomicU64::new(0);
// static STEAL_ATTEMPTS_RETRY: AtomicU64 = AtomicU64::new(0);

// static STEAL_FROM_LAST_VICTIM_SUCCESS: AtomicU64 = AtomicU64::new(0);
// static STEAL_FROM_LAST_VICTIM_FAIL: AtomicU64 = AtomicU64::new(0);

#[derive(Default)]
pub(super) struct ExecutionStatistics {
    steal_attempts_success: u64,
    steal_attempts_empty: u64,
    steal_attempts_retry: u64,
    steal_from_last_victim_success: u64,
    steal_from_last_victim_fail: u64,
}

impl ExecutionStatistics {
    pub(super) fn new() -> Self {
        Self {
            steal_attempts_success: 0,
            steal_attempts_empty: 0,
            steal_attempts_retry: 0,
            steal_from_last_victim_success: 0,
            steal_from_last_victim_fail: 0,
        }
    }

    pub(super) fn on_steal_attempt<T>(&mut self, result: &Steal<T>) {
        match result {
            Steal::Success(_) => self.steal_attempts_success += 1,
            Steal::Empty => self.steal_attempts_empty += 1,
            Steal::Retry => self.steal_attempts_retry += 1,
        }
    }

    pub(super) fn on_steal_from_last_victim<T>(&mut self, task: &Option<T>) {
        if task.is_some() {
            self.steal_from_last_victim_success += 1;
        } else {
            self.steal_from_last_victim_fail += 1;
        }
    }

    pub(super) fn merge(&mut self, other: &ExecutionStatistics) {
        self.steal_attempts_success += other.steal_attempts_success;
        self.steal_attempts_empty += other.steal_attempts_empty;
        self.steal_attempts_retry += other.steal_attempts_retry;
        self.steal_from_last_victim_success += other.steal_from_last_victim_success;
        self.steal_from_last_victim_fail += other.steal_from_last_victim_fail;
    }

    pub(super) fn print(&self) {
        println!("Steal attempts success: {}", self.steal_attempts_success);
        println!("Steal attempts empty: {}", self.steal_attempts_empty);
        println!("Steal attempts retry: {}", self.steal_attempts_retry);
        println!(
            "Steal from last victim success: {}",
            self.steal_from_last_victim_success
        );
        println!(
            "Steal from last victim fail: {}",
            self.steal_from_last_victim_fail
        );
    }
}
