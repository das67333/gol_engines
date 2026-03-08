use crossbeam::{deque::Steal, utils::CachePadded};
use std::{
    cell::RefCell,
    sync::atomic::{AtomicUsize, Ordering},
};

/// Newtype for raw timer ticks (CNTVCT_EL0) to prevent misuse.
#[derive(Clone, Copy)]
pub(super) struct Ticks(u64);

impl Ticks {
    #[inline(always)]
    pub(super) fn now() -> Self {
        let value: u64;
        unsafe {
            core::arch::asm!("mrs {0}, cntvct_el0", out(reg) value);
        }
        Self(value)
    }

    #[inline(always)]
    pub(super) fn elapsed_since(self, start: Ticks) -> Self {
        Self(self.0.wrapping_sub(start.0))
    }

    fn raw(self) -> u64 {
        self.0
    }
}

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

/// Metric kind for log2 histogram distributions.
/// Spin-count metrics store raw spin iterations.
/// TaskDuration stores raw timer ticks.
#[derive(Clone, Copy)]
#[repr(usize)]
pub(super) enum MetricKind {
    // Hashtable slot locks (spin count)
    NodeStoreLock = 0,
    BinodeCacheLock = 1,
    // PENDING -> PROCESSING status acquire (spin count)
    ProcessTask = 2,
    NotifyDep = 3,
    HandleDep = 4,
    HandleBiDep = 5,
    // Algorithm spin-wait on FINISHED (spin count)
    Node2Lanes = 6,
    UpdateNodeSync = 7,
    // Task duration (raw timer ticks)
    TaskDuration = 8,
}

impl MetricKind {
    const COUNT: usize = 9;
    const ALL: [Self; Self::COUNT] = [
        Self::NodeStoreLock,
        Self::BinodeCacheLock,
        Self::ProcessTask,
        Self::NotifyDep,
        Self::HandleDep,
        Self::HandleBiDep,
        Self::Node2Lanes,
        Self::UpdateNodeSync,
        Self::TaskDuration,
    ];

    fn label(self) -> &'static str {
        match self {
            Self::NodeStoreLock => "Spin [node_store_lock]",
            Self::BinodeCacheLock => "Spin [binode_cache_lock]",
            Self::ProcessTask => "Spin [process_task]",
            Self::NotifyDep => "Spin [notify_dep]",
            Self::HandleDep => "Spin [handle_dep]",
            Self::HandleBiDep => "Spin [handle_bi_dep]",
            Self::Node2Lanes => "Spin [node2lanes]",
            Self::UpdateNodeSync => "Spin [update_node_sync]",
            Self::TaskDuration => "Task duration",
        }
    }

    fn is_duration(self) -> bool {
        matches!(self, Self::TaskDuration)
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
    /// Unified log2 distributions for all metric kinds.
    distributions: [[u64; Self::DISTRIBUTION_BUCKETS]; MetricKind::COUNT],
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

/// Log2 bucket assignment. Bucket 0 = [0, 1), bucket i (i>=1) = [2^(i-1), 2^i).
fn value_to_bucket(value: u64) -> usize {
    let i = (value + 1).next_power_of_two().trailing_zeros();
    (i as usize).min(ExecutionStatistics::DISTRIBUTION_BUCKETS - 1)
}

/// Bin range for bucket i: [lo, hi).
/// Bucket 0 = [0, 1), bucket i (i>=1) = [2^(i-1), 2^i).
fn bin_range(i: usize) -> (f64, f64) {
    if i == 0 {
        (0.0, 1.0)
    } else {
        (2f64.powi(i as i32 - 1), 2f64.powi(i as i32))
    }
}

const PERCENTILES: &[(f64, &str)] = &[
    (0.50, "p50"),
    (0.9, "p(1)"),
    (0.99, "p(2)"),
    (0.999, "p(3)"),
    (0.9999, "p(4)"),
    (0.99999, "p(5)"),
    (0.999999, "p(6)"),
    (0.9999999, "p(7)"),
    (0.99999999, "p(8)"),
];

/// Compute percentile values from a histogram, assuming uniform distribution within each bin.
fn compute_percentiles(dist: &[u64]) -> Vec<f64> {
    let total: u64 = dist.iter().sum();
    if total == 0 {
        return vec![0.0; PERCENTILES.len()];
    }

    let mut results = Vec::with_capacity(PERCENTILES.len());
    let mut cumulative: u64 = 0;
    let mut pi = 0;

    for (i, &count) in dist.iter().enumerate() {
        if count == 0 {
            continue;
        }
        let prev_cumulative = cumulative;
        cumulative += count;

        while pi < PERCENTILES.len() {
            let target = PERCENTILES[pi].0 * total as f64;
            if cumulative as f64 >= target {
                let (lo, hi) = bin_range(i);
                let fraction = (target - prev_cumulative as f64) / count as f64;
                results.push(lo + fraction * (hi - lo));
                pi += 1;
            } else {
                break;
            }
        }
        if pi >= PERCENTILES.len() {
            break;
        }
    }
    while pi < PERCENTILES.len() {
        results.push(0.0);
        pi += 1;
    }
    results
}

fn format_ns(ns: f64) -> String {
    if ns < 1e3 {
        format!("{:.1}ns", ns)
    } else if ns < 1e6 {
        format!("{:.2}us", ns / 1e3)
    } else if ns < 1e9 {
        format!("{:.2}ms", ns / 1e6)
    } else {
        format!("{:.2}s", ns / 1e9)
    }
}

/// Format a count using scientific notation when shorter.
fn format_count(n: u64) -> String {
    let plain = format!("{}", n);
    let sci = format!("{:.1e}", n as f64);
    if sci.len() < plain.len() { sci } else { plain }
}

fn fmt_distribution(
    f: &mut std::fmt::Formatter<'_>,
    kind: MetricKind,
    dist: &[u64],
) -> std::fmt::Result {
    let total: u64 = dist.iter().sum();
    if total == 0 {
        return Ok(());
    }
    let percentiles = compute_percentiles(dist);
    let ns_per_tick = 1e9 / cntfrq() as f64;
    write!(f, "{:<30} {:>10}", kind.label(), format_count(total))?;
    for &value in &percentiles {
        if kind.is_duration() {
            write!(f, " {:>8}", format_ns(value * ns_per_tick))?;
        } else {
            write!(f, " {:>8}", format_count(value as u64))?;
        }
    }
    writeln!(f)
}

fn cntfrq() -> u64 {
    let value: u64;
    unsafe {
        core::arch::asm!("mrs {0}, cntfrq_el0", out(reg) value);
    }
    value
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

/// Record a value into a metric's log2 histogram.
pub(super) fn record_metric(value: u64, kind: MetricKind) {
    with_current_stats(|st| {
        st.distributions[kind as usize][value_to_bucket(value)] += 1;
    });
}

/// Record task duration from raw timer ticks.
pub(super) fn record_task_duration(ticks: Ticks) {
    record_metric(ticks.raw(), MetricKind::TaskDuration);
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
    const DISTRIBUTION_BUCKETS: usize = 40;

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
            distributions: [[0; Self::DISTRIBUTION_BUCKETS]; MetricKind::COUNT],
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
            .distributions
            .iter_mut()
            .zip(other.distributions.iter())
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
        // Percentile header
        write!(f, "{:<30} {:>10}", "", "total")?;
        for &(_, label) in PERCENTILES {
            write!(f, " {:>8}", label)?;
        }
        writeln!(f)?;
        for kind in MetricKind::ALL {
            fmt_distribution(f, kind, &self.distributions[kind as usize])?;
        }
        Ok(())
    }
}
