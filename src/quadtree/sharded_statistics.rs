use crossbeam::utils::CachePadded;
use std::{
    cell::RefCell,
    sync::atomic::{AtomicUsize, Ordering},
};

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

pub(super) struct ExecutionStatistics {
    // Steal attempts
    steal_success: u64,
    steal_empty: u64,
    steal_retry: u64,
    last_victim_steal_success: u64,
    last_victim_steal_fail: u64,
    // Hashtable slot lock (find_or_create)
    hashtable_lock_acquire_success: u64,
    hashtable_cmpxchg_fail: u64,
    /// Approximate distribution: bucket i counts acquisitions with spin_count in (2^(i-1), 2^i] (bucket 0 = 0 spins).
    hashtable_lock_spin_distribution: [u64; Self::SPIN_DISTRIBUTION_BUCKETS],
    // Status transitions (NOT_STARTED -> PROCESSING claim, PENDING -> PROCESSING acquire)
    status_claim_success: u64,
    status_claim_fail: u64,
    status_acquire_success: u64,
    status_acquire_cmpxchg_fail: u64,
    status_spin_on_processing: u64,
}

thread_local! {
    static CURRENT_STATS: RefCell<Option<Box<ExecutionStatistics>>> = RefCell::new(None);
}

/// Set the current thread's execution statistics sink (owned by the thread-local).
pub(super) fn set_current_execution_stats() {
    CURRENT_STATS.with(|cell| *cell.borrow_mut() = Some(Box::new(ExecutionStatistics::new())));
}

/// Take the current thread's execution statistics, if any. Clears the thread-local.
pub(super) fn take_current_execution_stats() -> Option<ExecutionStatistics> {
    CURRENT_STATS.with(|cell| cell.borrow_mut().take().map(|b| *b))
}

fn with_current_stats<R>(f: impl FnOnce(&mut ExecutionStatistics) -> R) {
    CURRENT_STATS.with(|cell| cell.borrow_mut().as_deref_mut().map(f));
}

fn spin_count_to_bucket(spin_count: u64) -> usize {
    let i = (spin_count + 1).next_power_of_two().trailing_zeros();
    (i as usize).min(ExecutionStatistics::SPIN_DISTRIBUTION_BUCKETS - 1)
}

/// Record successful hashtable lock acquisition with the given number of spin iterations.
/// Stored in buckets by (spin_count + 1).next_power_of_two() (approximate).
pub(super) fn record_hashtable_lock_acquired(spin_count: u64) {
    with_current_stats(|st| {
        st.hashtable_lock_acquire_success += 1;
        let b = spin_count_to_bucket(spin_count);
        st.hashtable_lock_spin_distribution[b] += 1;
    });
}

/// Record one failed compare_exchange when acquiring hashtable slot lock.
pub(super) fn record_hashtable_cmpxchg_fail() {
    with_current_stats(|st| st.hashtable_cmpxchg_fail += 1);
}

/// Record NOT_STARTED -> PROCESSING claim success (this thread claimed).
pub(super) fn record_status_claim_success() {
    with_current_stats(|st| st.status_claim_success += 1);
}

/// Record NOT_STARTED -> PROCESSING claim failure (another thread claimed).
pub(super) fn record_status_claim_fail() {
    with_current_stats(|st| st.status_claim_fail += 1);
}

/// Record PENDING -> PROCESSING acquire success.
pub(super) fn record_status_acquire_success() {
    with_current_stats(|st| st.status_acquire_success += 1);
}

/// Record one failed compare_exchange in PENDING -> PROCESSING acquire.
pub(super) fn record_status_acquire_cmpxchg_fail() {
    with_current_stats(|st| st.status_acquire_cmpxchg_fail += 1);
}

/// Record one spin iteration waiting for PROCESSING to end.
pub(super) fn record_status_spin_on_processing() {
    with_current_stats(|st| st.status_spin_on_processing += 1);
}

/// Record steal attempt outcome (thread-local).
pub(super) fn record_steal_success() {
    with_current_stats(|st| st.steal_success += 1);
}

pub(super) fn record_steal_empty() {
    with_current_stats(|st| st.steal_empty += 1);
}

pub(super) fn record_steal_retry() {
    with_current_stats(|st| st.steal_retry += 1);
}

pub(super) fn record_last_victim_steal_success() {
    with_current_stats(|st| st.last_victim_steal_success += 1);
}

pub(super) fn record_last_victim_steal_fail() {
    with_current_stats(|st| st.last_victim_steal_fail += 1);
}

impl ExecutionStatistics {
    const SPIN_DISTRIBUTION_BUCKETS: usize = 40;

    pub(super) fn new() -> Self {
        Self {
            steal_success: 0,
            steal_empty: 0,
            steal_retry: 0,
            last_victim_steal_success: 0,
            last_victim_steal_fail: 0,
            hashtable_lock_acquire_success: 0,
            hashtable_cmpxchg_fail: 0,
            hashtable_lock_spin_distribution: [0; Self::SPIN_DISTRIBUTION_BUCKETS],
            status_claim_success: 0,
            status_claim_fail: 0,
            status_acquire_success: 0,
            status_acquire_cmpxchg_fail: 0,
            status_spin_on_processing: 0,
        }
    }

    pub(super) fn merge_from(&mut self, other: &ExecutionStatistics) {
        self.steal_success += other.steal_success;
        self.steal_empty += other.steal_empty;
        self.steal_retry += other.steal_retry;
        self.last_victim_steal_success += other.last_victim_steal_success;
        self.last_victim_steal_fail += other.last_victim_steal_fail;
        self.hashtable_lock_acquire_success += other.hashtable_lock_acquire_success;
        self.hashtable_cmpxchg_fail += other.hashtable_cmpxchg_fail;
        for (i, v) in other.hashtable_lock_spin_distribution.iter().enumerate() {
            self.hashtable_lock_spin_distribution[i] += v;
        }
        self.status_claim_success += other.status_claim_success;
        self.status_claim_fail += other.status_claim_fail;
        self.status_acquire_success += other.status_acquire_success;
        self.status_acquire_cmpxchg_fail += other.status_acquire_cmpxchg_fail;
        self.status_spin_on_processing += other.status_spin_on_processing;
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
        writeln!(
            f,
            "Steal from last victim fail: {}",
            self.last_victim_steal_fail
        )?;
        writeln!(
            f,
            "Hashtable lock acquire success: {}",
            self.hashtable_lock_acquire_success
        )?;
        writeln!(
            f,
            "Hashtable cmpxchg fail (lock acquire): {}",
            self.hashtable_cmpxchg_fail
        )?;
        {
            writeln!(f, "Hashtable lock spin distribution (by spins, count):")?;
            for (i, &v) in self
                .hashtable_lock_spin_distribution
                .iter()
                .filter(|&v| *v != 0)
                .enumerate()
            {
                let min_spin = if i == 0 { 0 } else { 1u64 << (i - 1) };
                let max_spin = (1u64 << i) - 1;
                writeln!(f, "\t{}..={} -> {}", min_spin, max_spin, v)?;
            }
        }
        writeln!(f, "Status claim success: {}", self.status_claim_success)?;
        writeln!(
            f,
            "Status claim fail (NOT_STARTED->PROCESSING): {}",
            self.status_claim_fail
        )?;
        writeln!(f, "Status acquire success: {}", self.status_acquire_success)?;
        writeln!(
            f,
            "Status acquire cmpxchg fail (PENDING->PROCESSING): {}",
            self.status_acquire_cmpxchg_fail
        )?;
        write!(
            f,
            "Status spin on PROCESSING: {}",
            self.status_spin_on_processing
        )
    }
}
