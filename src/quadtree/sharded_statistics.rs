use crossbeam::{deque::Steal, utils::CachePadded};
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

#[derive(Clone, Copy)]
#[repr(usize)]
pub(super) enum SpinlockKind {
    // Hashtable slot locks
    NodeStoreLock = 0,
    BinodeCacheLock = 1,
    // PENDING -> PROCESSING status acquire
    ProcessTask = 2,
    NotifyDep = 3,
    HandleDep = 4,
    HandleBiDep = 5,
    // Algorithm spin-wait on FINISHED
    Node2Lanes = 6,
    UpdateNodeSync = 7,
}

impl SpinlockKind {
    const COUNT: usize = 8;
    const ALL: [Self; Self::COUNT] = [
        Self::NodeStoreLock,
        Self::BinodeCacheLock,
        Self::ProcessTask,
        Self::NotifyDep,
        Self::HandleDep,
        Self::HandleBiDep,
        Self::Node2Lanes,
        Self::UpdateNodeSync,
    ];

    fn label(self) -> &'static str {
        match self {
            Self::NodeStoreLock => "node_store_lock",
            Self::BinodeCacheLock => "binode_cache_lock",
            Self::ProcessTask => "process_task",
            Self::NotifyDep => "notify_dep",
            Self::HandleDep => "handle_dep",
            Self::HandleBiDep => "handle_bi_dep",
            Self::Node2Lanes => "node2lanes",
            Self::UpdateNodeSync => "update_node_sync",
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
    // Hashtable CAS failures (across all hashtable types)
    hashtable_cmpxchg_fail: u64,
    // Status transitions (NOT_STARTED -> PROCESSING claim)
    status_claim_success: u64,
    status_claim_fail: u64,
    /// Per-spinlock-kind spin distributions.
    spinlock_distributions: [[u64; Self::SPIN_DISTRIBUTION_BUCKETS]; SpinlockKind::COUNT],
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

fn fmt_spin_distribution(
    f: &mut std::fmt::Formatter<'_>,
    label: &str,
    dist: &[u64],
) -> std::fmt::Result {
    writeln!(f, "{label} (by spins, count):")?;
    for (i, &v) in dist.iter().enumerate().filter(|(_, v)| **v != 0) {
        let min_spin = if i == 0 { 0 } else { 1u64 << (i - 1) };
        let max_spin = (1u64 << i) - 1;
        writeln!(f, "\t{}..={} -> {}", min_spin, max_spin, v)?;
    }
    Ok(())
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

/// Record successful spinlock acquisition with the given number of spin iterations.
pub(super) fn record_spinlock_acquired(spin_count: u64, kind: SpinlockKind) {
    with_current_stats(|st| {
        let dist = &mut st.spinlock_distributions[kind as usize];
        dist[spin_count_to_bucket(spin_count)] += 1;
    });
}

/// Record steal attempt outcome (thread-local).
pub(super) fn record_steal<Task>(result: &Steal<Task>) {
    with_current_stats(|st| match result {
        Steal::Success(_) => st.steal_success += 1,
        Steal::Empty => st.steal_empty += 1,
        Steal::Retry => st.steal_retry += 1,
    });
}

pub(super) fn record_last_victim_steal<Task>(result: &Option<Task>) {
    with_current_stats(|st| {
        if result.is_some() {
            st.last_victim_steal_success += 1
        } else {
            st.last_victim_steal_fail += 1
        }
    });
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
            hashtable_cmpxchg_fail: 0,
            status_claim_success: 0,
            status_claim_fail: 0,
            spinlock_distributions: [[0; Self::SPIN_DISTRIBUTION_BUCKETS]; SpinlockKind::COUNT],
        }
    }

    pub(super) fn merge_from(&mut self, other: &ExecutionStatistics) {
        self.steal_success += other.steal_success;
        self.steal_empty += other.steal_empty;
        self.steal_retry += other.steal_retry;
        self.last_victim_steal_success += other.last_victim_steal_success;
        self.last_victim_steal_fail += other.last_victim_steal_fail;
        self.hashtable_cmpxchg_fail += other.hashtable_cmpxchg_fail;
        self.status_claim_success += other.status_claim_success;
        self.status_claim_fail += other.status_claim_fail;
        for (dst_dist, src_dist) in self
            .spinlock_distributions
            .iter_mut()
            .zip(other.spinlock_distributions.iter())
        {
            for (dst, src) in dst_dist.iter_mut().zip(src_dist.iter()) {
                *dst += *src;
            }
        }
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
            "Hashtable cmpxchg fail (lock acquire): {}",
            self.hashtable_cmpxchg_fail
        )?;
        writeln!(f, "Status claim success: {}", self.status_claim_success)?;
        writeln!(
            f,
            "Status claim fail (NOT_STARTED->PROCESSING): {}",
            self.status_claim_fail
        )?;
        for kind in SpinlockKind::ALL {
            let dist = &self.spinlock_distributions[kind as usize];
            let total: u64 = dist.iter().sum();
            if total > 0 {
                fmt_spin_distribution(
                    f,
                    &format!("Spinlock [{}] ({} total)", kind.label(), total),
                    dist,
                )?;
            }
        }
        Ok(())
    }
}
