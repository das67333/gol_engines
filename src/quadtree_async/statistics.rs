//! A thread-local statistics collector for quadtree operations.
use crate::{MAX_TASKS_COUNT, MIN_TASK_SPAWN_SIZE_LOG2, TASKS_SPAWN_COUNT};
use std::cell::Cell;
use std::sync::atomic::{AtomicU64, AtomicU8, AtomicUsize, Ordering};

// Enforce singleton: only one ExecutionStatistics may be instantiated.
static INSTANCE_COUNT: AtomicU8 = AtomicU8::new(0);

static ACTIVE_TASKS_COUNT: AtomicU64 = AtomicU64::new(0);

/// Global accumulated count flushed from all threads.
static LENGTH_GLOBAL_COUNT: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    static LENGTH_LOCAL_COUNT: Cell<u8> = const { Cell::new(0) };
}

/// Thread-safe execution statistics collector with efficient batched counters.
///
/// This struct provides thread-local counters that periodically flush to a global
/// atomic counter to minimize contention. It helps track quadtree node operations
/// and determine when to spawn new tasks or poison MemoryManager
/// based on execution metrics.
///
/// Uses 8-bit local counters with a fixed threshold of 256 operations before
/// flushing to the global counter for efficiency.
pub(super) struct ExecutionStatistics {
    length_limit: usize,
}

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
        Self {
            length_limit: capacity * 3 / 4,
        }
    }

    /// Determines if a new task should be spawned based on current execution metrics.
    ///
    /// # Returns
    /// `true` if the system should spawn a new task, `false` otherwise.
    pub(super) fn should_spawn(&self, size_log2: u32) -> bool {
        size_log2 >= MIN_TASK_SPAWN_SIZE_LOG2.load(Ordering::Relaxed)
            && ACTIVE_TASKS_COUNT.load(Ordering::Relaxed) < MAX_TASKS_COUNT
    }

    /// Checks if a node should be poisoned upon creation.
    ///
    /// Increments the local length counter and potentially flushes to global counter.
    ///
    /// # Returns
    /// `true` if the node should be poisoned, `false` otherwise
    #[inline]
    pub(super) fn should_poison_on_creation(&self) -> bool {
        let mut result = false;
        LENGTH_LOCAL_COUNT.with(|cell| {
            let new_value = cell.get().wrapping_add(1);
            cell.set(new_value);

            // If we wrapped around (new_value is 0), flush 256 to global
            if new_value == 0
                && LENGTH_GLOBAL_COUNT.fetch_add(256, Ordering::Relaxed) > self.length_limit
            {
                result = true;
            }
        });

        result
    }

    pub(super) fn reset(&self) {
        LENGTH_GLOBAL_COUNT.store(0, Ordering::Relaxed);
    }
}

impl Drop for ExecutionStatistics {
    fn drop(&mut self) {
        INSTANCE_COUNT.fetch_sub(1, Ordering::SeqCst);
        LENGTH_GLOBAL_COUNT.store(0, Ordering::Relaxed);
    }
}

pub(super) struct TasksCountGuard(u8);

impl TasksCountGuard {
    pub(super) fn new(count: u8) -> Self {
        TASKS_SPAWN_COUNT.fetch_add(count as u64, Ordering::Relaxed);
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
        LENGTH_GLOBAL_COUNT.load(Ordering::Relaxed)
    }

    #[test]
    #[serial]
    fn single_thread_increments() {
        let stats = ExecutionStatistics::new(0);
        let initial = get_approx();
        for _ in 0..256 {
            stats.should_poison_on_creation();
        }
        assert_eq!(get_approx(), initial + 256);
    }

    #[test]
    #[serial]
    fn multi_threaded_increments() {
        let stats = ExecutionStatistics::new(0);
        let initial = get_approx();

        std::thread::scope(|s| {
            for _ in 0..4 {
                let c = &stats;
                s.spawn(move || {
                    for _ in 0..1024 {
                        c.should_poison_on_creation();
                    }
                });
            }
        });
        assert_eq!(get_approx(), initial + 4 * 1024);
    }
}
