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

    pub(super) fn inc_global(&self) {
        self.global.fetch_add(1, Ordering::Relaxed);
    }

    pub(super) fn len_exact(&self) -> usize {
        let shards_sum_exact = self
            .shards
            .iter()
            .map(|shard| shard.load(Ordering::Relaxed))
            .sum::<usize>();

        self.global.load(Ordering::Relaxed) + shards_sum_exact
    }

    pub(super) fn shard(&self, shard_idx: usize) -> LengthShard<'_> {
        LengthShard {
            local: &self.shards[shard_idx],
            global: &self.global,
        }
    }

    pub(super) fn len_upper_bound(&self) -> usize {
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

#[derive(Default)]
pub(super) struct ExecutionStatistics {
    steal_success: u64,
    steal_empty: u64,
    steal_retry: u64,
    last_victim_steal_success: u64,
    last_victim_steal_fail: u64,
}

impl ExecutionStatistics {
    pub(super) fn record_steal_attempt<T>(&mut self, result: &Steal<T>) {
        match result {
            Steal::Success(_) => self.steal_success += 1,
            Steal::Empty => self.steal_empty += 1,
            Steal::Retry => self.steal_retry += 1,
        }
    }

    pub(super) fn record_last_victim_steal<T>(&mut self, task: &Option<T>) {
        if task.is_some() {
            self.last_victim_steal_success += 1;
        } else {
            self.last_victim_steal_fail += 1;
        }
    }

    pub(super) fn merge_from(&mut self, other: &ExecutionStatistics) {
        self.steal_success += other.steal_success;
        self.steal_empty += other.steal_empty;
        self.steal_retry += other.steal_retry;
        self.last_victim_steal_success += other.last_victim_steal_success;
        self.last_victim_steal_fail += other.last_victim_steal_fail;
    }
}

impl std::fmt::Display for ExecutionStatistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Steal attempts success: {}", self.steal_success)?;
        writeln!(f, "Steal attempts empty: {}", self.steal_empty)?;
        writeln!(f, "Steal attempts retry: {}", self.steal_retry)?;
        writeln!(
            f,
            "Steal from last victim success: {}",
            self.last_victim_steal_success
        )?;
        write!(
            f,
            "Steal from last victim fail: {}",
            self.last_victim_steal_fail
        )
    }
}
