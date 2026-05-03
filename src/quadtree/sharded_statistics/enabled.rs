use super::MetricKind;
use crossbeam::deque::Steal;
use std::cell::RefCell;

// -- Ticks --------------------------------------------------------------

#[derive(Clone, Copy)]
pub struct Ticks(u64);

impl Ticks {
    #[inline(always)]
    pub fn now() -> Self {
        Self(Self::read_timestamp())
    }

    #[inline(always)]
    pub fn elapsed_since(self, start: Ticks) -> Self {
        Self(self.0.wrapping_sub(start.0))
    }

    fn raw(self) -> u64 {
        self.0
    }

    #[cfg(target_arch = "aarch64")]
    #[inline(always)]
    fn read_timestamp() -> u64 {
        let value: u64;
        unsafe {
            core::arch::asm!("mrs {0}, cntvct_el0", out(reg) value);
        }
        value
    }

    #[cfg(target_arch = "x86_64")]
    #[inline(always)]
    fn read_timestamp() -> u64 {
        unsafe {
            core::arch::x86_64::_rdtsc()
        }
    }
}

// -- ExecutionStatistics ------------------------------------------------

pub struct ExecutionStatistics {
    // Steal attempts
    steal_success: u64,
    steal_empty: u64,
    steal_retry: u64,
    last_victim_steal_success: u64,
    last_victim_steal_fail: u64,
    // Status transitions (NOT_STARTED -> PROCESSING claim)
    status_claim_success: u64,
    status_claim_fail: u64,
    /// Unified log2 distributions for all metric kinds.
    distributions: [[u64; Self::DISTRIBUTION_BUCKETS]; Self::METRIC_COUNT],
}

impl ExecutionStatistics {
    const DISTRIBUTION_BUCKETS: usize = 40;
    const METRIC_COUNT: usize = 6;

    pub fn new() -> Self {
        Self {
            steal_success: 0,
            steal_empty: 0,
            steal_retry: 0,
            last_victim_steal_success: 0,
            last_victim_steal_fail: 0,
            status_claim_success: 0,
            status_claim_fail: 0,
            distributions: [[0; Self::DISTRIBUTION_BUCKETS]; Self::METRIC_COUNT],
        }
    }

    pub fn merge_from(&mut self, other: &ExecutionStatistics) {
        self.steal_success += other.steal_success;
        self.steal_empty += other.steal_empty;
        self.steal_retry += other.steal_retry;
        self.last_victim_steal_success += other.last_victim_steal_success;
        self.last_victim_steal_fail += other.last_victim_steal_fail;
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

// -- MetricKind presentation helpers (private to this module) ----------

impl MetricKind {
    const COUNT: usize = ExecutionStatistics::METRIC_COUNT;
    const ALL: [Self; Self::COUNT] = [
        Self::ProcessTask,
        Self::NotifyDep,
        Self::HandleDep,
        Self::HandleBiDep,
        Self::Node2Lanes,
        Self::TaskDuration,
    ];

    fn label(self) -> &'static str {
        match self {
            Self::ProcessTask => "Spin [process_task]",
            Self::NotifyDep => "Spin [notify_dep]",
            Self::HandleDep => "Spin [handle_dep]",
            Self::HandleBiDep => "Spin [handle_bi_dep]",
            Self::Node2Lanes => "Spin [node2lanes]",
            Self::TaskDuration => "Task duration",
        }
    }

    fn is_duration(self) -> bool {
        matches!(self, Self::TaskDuration)
    }
}

// -- Thread-local sink --------------------------------------------------

thread_local! {
    static CURRENT_STATS: RefCell<Option<Box<ExecutionStatistics>>> = const { RefCell::new(None) };
}

fn with_current_stats<R>(f: impl FnOnce(&mut ExecutionStatistics) -> R) {
    CURRENT_STATS.with(|cell| cell.borrow_mut().as_deref_mut().map(f));
}

/// Set the current thread's execution statistics sink (owned by the thread-local).
pub fn set_current_execution_stats() {
    CURRENT_STATS
        .with(|cell| *cell.borrow_mut() = Some(Box::new(ExecutionStatistics::new())));
}

/// Take the current thread's execution statistics, if any. Clears the thread-local.
pub fn take_current_execution_stats() -> Option<ExecutionStatistics> {
    CURRENT_STATS.with(|cell| cell.borrow_mut().take().map(|b| *b))
}

// -- Recording API ------------------------------------------------------

/// Record NOT_STARTED -> PROCESSING claim success (this thread claimed).
pub fn record_status_claim_success() {
    with_current_stats(|st| st.status_claim_success += 1);
}

/// Record NOT_STARTED -> PROCESSING claim failure (another thread claimed).
pub fn record_status_claim_fail() {
    with_current_stats(|st| st.status_claim_fail += 1);
}

/// Record a value into a metric's log2 histogram.
pub fn record_metric(value: u64, kind: MetricKind) {
    with_current_stats(|st| {
        st.distributions[kind as usize][value_to_bucket(value)] += 1;
    });
}

/// Record task duration from raw timer ticks.
pub fn record_task_duration(ticks: Ticks) {
    record_metric(ticks.raw(), MetricKind::TaskDuration);
}

/// Record steal attempt outcome (thread-local).
pub fn record_steal<Task>(result: &Steal<Task>) {
    with_current_stats(|st| match result {
        Steal::Success(_) => st.steal_success += 1,
        Steal::Empty => st.steal_empty += 1,
        Steal::Retry => st.steal_retry += 1,
    });
}

pub fn record_last_victim_steal<Task>(result: &Option<Task>) {
    with_current_stats(|st| {
        if result.is_some() {
            st.last_victim_steal_success += 1
        } else {
            st.last_victim_steal_fail += 1
        }
    });
}

// -- Percentile / formatting helpers -----------------------------------

/// Log2 bucket assignment. Bucket 0 = {0}, bucket i (i>=1) = [2^(i-1), 2^i - 1].
fn value_to_bucket(value: u64) -> usize {
    let i = (value + 1).next_power_of_two().trailing_zeros();
    (i as usize).min(ExecutionStatistics::DISTRIBUTION_BUCKETS - 1)
}

/// Inclusive bin range for bucket i: [lo, hi].
/// Bucket 0 = {0}, bucket i (i>=1) = [2^(i-1), 2^i - 1].
fn bin_range(i: usize) -> (f64, f64) {
    if i == 0 {
        (0.0, 0.0)
    } else {
        (2f64.powi(i as i32 - 1), 2f64.powi(i as i32) - 1.0)
    }
}

// Nines notation: p(n) = (1 - 10^-n)th percentile, e.g. p(2) = 99th, p(3) = 99.9th.
const PERCENTILES: &[(f64, &str)] = &[
    (0.50, "p50"),
    (0.9, "p(1)"),
    (0.99, "p(2)"),
    (0.999, "p(3)"),
    (0.9999, "p(4)"),
    (0.99999, "p(5)"),
    (0.999999, "p(6)"),
    (1.0, "max"),
];

/// Compute percentile values from a histogram, assuming uniform distribution within each bin.
fn compute_percentiles(dist: &[u64]) -> Vec<f64> {
    assert!(
        PERCENTILES.windows(2).all(|w| w[0].0 <= w[1].0),
        "PERCENTILES must be sorted in ascending order"
    );
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

/// Query the timer frequency (ticks per second) for the current platform.
fn timer_frequency() -> u64 {
    #[cfg(target_arch = "aarch64")]
    {
        let value: u64;
        unsafe {
            core::arch::asm!("mrs {0}, cntfrq_el0", out(reg) value);
        }
        value
    }

    #[cfg(target_arch = "x86_64")]
    {
        // TSC frequency is not trivially queryable; use a reasonable
        // estimate.  For accurate results consider calibrating at startup.
        // We default to a typical ~3 GHz.
        3_000_000_000u64
    }
}

fn fmt_distribution(
    f: &mut std::fmt::Formatter<'_>,
    kind: MetricKind,
    dist: &[u64],
) -> std::fmt::Result {
    let cnt: u64 = dist.iter().sum();
    if cnt == 0 {
        return Ok(());
    }
    let sum: u64 = dist
        .iter()
        .enumerate()
        .map(|(i, &c)| {
            let (lo, hi) = bin_range(i);
            (lo + hi) * 0.5 * c as f64
        })
        .sum::<f64>() as u64;
    let percentiles = compute_percentiles(dist);
    let ns_per_tick = 1e9 / timer_frequency() as f64;
    let nnz: u64 = cnt - dist[0];
    let sum_str = if kind.is_duration() {
        format_ns(sum as f64 * ns_per_tick)
    } else {
        format_count(sum)
    };

    write!(
        f,
        "{:<30} {:>10} {:>10} {:>10}",
        kind.label(),
        sum_str,
        format_count(cnt),
        format_count(nnz)
    )?;
    for &value in &percentiles {
        if kind.is_duration() {
            write!(f, " {:>8}", format_ns(value * ns_per_tick))?;
        } else {
            write!(f, " {:>8}", format_count(value as u64))?;
        }
    }
    writeln!(f)
}

impl std::fmt::Display for ExecutionStatistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "Steal attempts: {} ok / {} empty / {} retry",
            self.steal_success, self.steal_empty, self.steal_retry
        )?;
        writeln!(
            f,
            "Last-victim steals: {} ok / {} fail",
            self.last_victim_steal_success, self.last_victim_steal_fail
        )?;
        writeln!(
            f,
            "Status claims: {} ok / {} fail",
            self.status_claim_success, self.status_claim_fail
        )?;
        // Percentile header
        write!(f, "{:<30} {:>10} {:>10} {:>10}", "", "sum", "cnt", "nnz")?;
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
