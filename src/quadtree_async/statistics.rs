//! A thread-local statistics collector for quadtree operations.
use crate::{MAX_TASKS_COUNT, MIN_TASK_SPAWN_SHIFT, TASKS_SPAWNED_COUNT};
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, AtomicUsize, Ordering};

// Enforce singleton: only one ExecutionStatistics may be instantiated.
static INSTANCE_COUNT: AtomicU8 = AtomicU8::new(0);

/// Global count of running tokio tasks.
static ACTIVE_TASKS_COUNT: AtomicU64 = AtomicU64::new(0);

/// The maximum number of concurrent сontainers whose length is tracked.
/// Currently first is used for the MemoryManager,
/// and the second for the StreamLifeCache.
const MAX_TRACKED_CONTAINERS: usize = 2;

/// Global accumulated lengths flushed from all threads.
pub static LENGTH_GLOBAL_COUNT: [AtomicUsize; MAX_TRACKED_CONTAINERS] =
    [AtomicUsize::new(0), AtomicUsize::new(0)];

thread_local! {
    static LENGTH_LOCAL_COUNT: Cell<[u8; MAX_TRACKED_CONTAINERS]> = const { Cell::new([0; MAX_TRACKED_CONTAINERS]) };
    static SIZE_LOG2_ACCUMULATOR: Cell<u32> = const { Cell::new(0) };
}

const ACCUMULATOR_CAPACITY: u32 = 256;

static LENGTH_LIMIT: AtomicUsize = AtomicUsize::new(0);

/// if true, tracked hashtables are poisoned and should be cleared.
static POISONED: AtomicBool = AtomicBool::new(false);

/// Thread-safe execution statistics collector with efficient batched counters.
///
/// This struct provides thread-local counters that periodically flush to a global
/// atomic counter to minimize contention. It helps track quadtree node operations
/// and determine when to spawn new tasks or poison hashtables
/// based on execution metrics.
///
/// Uses 8-bit local counters with a fixed threshold of 256 operations before
/// flushing to the global counter for efficiency.
pub(super) struct ExecutionStatistics;

impl ExecutionStatistics {
    /// Creates a new singleton statistics tracker with the specified capacity.
    ///
    /// # Arguments
    /// * `cap_log2` - Log2 of the capacity, used to calculate operation limits
    ///
    /// # Panics
    /// Panics if more than one instance is created.
    pub(super) fn new(cap_log2: u32) -> Self {
        let prev = INSTANCE_COUNT.fetch_add(1, Ordering::SeqCst);
        assert!(prev == 0, "ExecutionStatistics must be a singleton");
        let capacity = 1usize.checked_shl(cap_log2).unwrap();
        LENGTH_LIMIT.store(capacity * 3 / 4, Ordering::Relaxed);
        Self {}
    }

    /// Determines if a new task should be spawned based on current execution metrics.
    ///
    /// # Returns
    /// `true` if the system should spawn a new task, `false` otherwise.
    #[inline]
    pub(super) fn should_spawn(size_log2: u32) -> bool {
        let min_task_spawn_size_log2 = SIZE_LOG2_ACCUMULATOR.with(|cell| {
            let acc = cell.get();
            let new_acc = (ACCUMULATOR_CAPACITY - 1) * acc / ACCUMULATOR_CAPACITY + size_log2;
            cell.set(new_acc);
            acc / ACCUMULATOR_CAPACITY
        });
        size_log2 >= min_task_spawn_size_log2 + MIN_TASK_SPAWN_SHIFT
            && ACTIVE_TASKS_COUNT.load(Ordering::Relaxed) < MAX_TASKS_COUNT
    }

    pub(super) fn get_min_task_spawn_size_log2() -> u32 {
        SIZE_LOG2_ACCUMULATOR.with(|cell| cell.get() / ACCUMULATOR_CAPACITY)
    }

    /// Checks if an insertion overfills the container.
    ///
    /// Increments the local length counter and potentially flushes to global counter.
    #[inline]
    pub(super) fn on_insertion<const I: usize>() {
        LENGTH_LOCAL_COUNT.with(|cell| {
            let mut value = cell.get();
            value[I] = value[I].wrapping_add(1);
            cell.set(value);

            // If we wrapped around (new_value is 0), flush 256 to global
            if value[I] == 0
                && LENGTH_GLOBAL_COUNT[I].fetch_add(256, Ordering::Relaxed)
                    > LENGTH_LIMIT.load(Ordering::Relaxed)
            {
                POISONED.store(true, Ordering::Relaxed);
            }
        });
    }

    #[inline]
    pub(super) fn is_poisoned() -> bool {
        POISONED.load(Ordering::Relaxed)
    }

    pub(super) fn reset() {
        for x in LENGTH_GLOBAL_COUNT.iter() {
            x.store(0, Ordering::Relaxed);
        }
        POISONED.store(false, Ordering::Relaxed);
    }
}

impl Drop for ExecutionStatistics {
    fn drop(&mut self) {
        INSTANCE_COUNT.fetch_sub(1, Ordering::SeqCst);
        Self::reset();
    }
}

pub(super) struct TasksCountGuard(u8);

impl TasksCountGuard {
    pub(super) fn new(count: u8) -> Self {
        TASKS_SPAWNED_COUNT.fetch_add(count as u64, Ordering::Relaxed);
        ACTIVE_TASKS_COUNT.fetch_add(count as u64, Ordering::Relaxed);
        Self(count)
    }
}

impl Drop for TasksCountGuard {
    fn drop(&mut self) {
        ACTIVE_TASKS_COUNT.fetch_sub(self.0 as u64, Ordering::Relaxed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    fn get_approx() -> usize {
        LENGTH_GLOBAL_COUNT[0].load(Ordering::Relaxed)
    }

    #[test]
    #[serial]
    fn single_thread_increments() {
        let _stats = ExecutionStatistics::new(0);
        let initial = get_approx();
        for _ in 0..256 {
            ExecutionStatistics::on_insertion::<0>();
        }
        assert_eq!(get_approx(), initial + 256);
    }

    #[test]
    #[serial]
    fn multi_threaded_increments() {
        let _stats = ExecutionStatistics::new(0);
        let initial = get_approx();

        std::thread::scope(|s| {
            for _ in 0..4 {
                s.spawn(move || {
                    for _ in 0..1024 {
                        ExecutionStatistics::on_insertion::<0>();
                    }
                });
            }
        });
        assert_eq!(get_approx(), initial + 4 * 1024);
    }
}
