//! A distributed counter with sharded local counters and a global aggregator.
//!
//! The counter is split into shards that can be incremented independently with minimal
//! contention. Each shard periodically flushes to a shared global value when it exceeds
//! a threshold, providing a tradeoff between performance and accuracy.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

/// Threshold at which a shard flushes its local value to the global counter.
/// It must be an even number.
const FLUSH_THRESHOLD: u64 = 256;

/// A single shard of the distributed counter.
///
/// Shards accumulate increments locally and flush to the global counter
/// when the local value exceeds `FLUSH_THRESHOLD`.
pub(super) struct CounterShard {
    /// Local counter for this shard.
    local: AtomicU64,
    /// Shared global counter that all shards flush to.
    global: Arc<AtomicU64>,
    /// Maximum possible deviation of approximate_value from the true value.
    max_error: u64,
}

impl CounterShard {
    /// Increments the counter by 1.
    ///
    /// If the local value exceeds the flush threshold, it flushes to the global counter.
    pub(super) fn increment(&self) {
        if self.local.fetch_add(1, Ordering::Relaxed) + 1 == FLUSH_THRESHOLD {
            self.flush();
        }
    }

    /// Flushes the local counter to the global counter.
    fn flush(&self) {
        self.global
            .fetch_add(self.local.swap(0, Ordering::Relaxed), Ordering::Relaxed);
    }

    /// Returns the approximate value of the entire distributed counter.
    ///
    /// This reads the global counter but does not include unflushed local values
    /// from other shards, so the result may be lower than the true value.
    pub(super) fn approximate_value(&self) -> u64 {
        self.global.load(Ordering::Relaxed) + self.max_error
    }

    /// Returns the maximum possible error from the true value.
    pub(super) fn max_error(&self) -> u64 {
        self.max_error
    }
}

impl Drop for CounterShard {
    fn drop(&mut self) {
        // Flush any remaining local value to global on drop.
        self.flush();
    }
}

/// The global distributed counter that owns references to all shards.
///
/// Provides exact counting by aggregating all shard values.
pub(super) struct DistributedCounter {
    /// The shared global counter value.
    global: Arc<AtomicU64>,
    /// References to all shards for exact counting.
    shards: Vec<Arc<CounterShard>>,
}

impl DistributedCounter {
    /// Creates a new distributed counter with the specified number of shards.
    ///
    /// # Arguments
    /// * `shard_count` - The number of shards to create.
    ///
    /// # Returns
    /// A tuple of the global counter and a vector of shard handles.
    pub(super) fn new(shard_count: usize) -> (Self, Vec<Arc<CounterShard>>) {
        let global = Arc::new(AtomicU64::new(0));
        let mut shards = Vec::with_capacity(shard_count);

        for _ in 0..shard_count {
            let shard = Arc::new(CounterShard {
                local: AtomicU64::new(0),
                global: Arc::clone(&global),
                max_error: FLUSH_THRESHOLD / 2 * shard_count as u64,
            });
            shards.push(shard);
        }

        let shard_refs = shards.clone();
        (Self { global, shards }, shard_refs)
    }

    /// Returns the exact value of the counter.
    ///
    /// This aggregates the global value plus all unflushed local values from shards.
    pub(super) fn exact_value(&self) -> u64 {
        let global = self.global.load(Ordering::Relaxed);
        let locals: u64 = self
            .shards
            .iter()
            .map(|s| s.local.load(Ordering::Relaxed))
            .sum();
        global + locals
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_shard_increment() {
        let (counter, shards) = DistributedCounter::new(1);
        let shard = &shards[0];

        for _ in 0..100 {
            shard.increment();
        }

        assert_eq!(counter.exact_value(), 100);
    }

    #[test]
    fn flush_on_threshold() {
        let (counter, shards) = DistributedCounter::new(1);
        let shard = &shards[0];

        // Increment up to threshold
        for _ in 0..FLUSH_THRESHOLD {
            shard.increment();
        }

        // After reaching threshold, value should be flushed to global
        assert_eq!(counter.global.load(Ordering::Relaxed), FLUSH_THRESHOLD);
        assert_eq!(counter.exact_value(), FLUSH_THRESHOLD);
    }

    #[test]
    fn multi_shard_exact_value() {
        let (counter, shards) = DistributedCounter::new(4);

        // Each shard increments a different number of times
        for (i, shard) in shards.iter().enumerate() {
            for _ in 0..((i + 1) * 50) {
                shard.increment();
            }
        }

        // 50 + 100 + 150 + 200 = 500
        assert_eq!(counter.exact_value(), 500);
    }

    #[test]
    fn approximate_value_bounds() {
        let (counter, shards) = DistributedCounter::new(4);

        for _ in 0..100 {
            for shard in &shards {
                shard.increment();

                let exact = counter.exact_value();
                let approx = shards[0].approximate_value();
                let max_dev = shards[0].max_error();
    
                // Approximate value should be within max_error of exact
                assert!(exact.abs_diff(approx) <= max_dev);
            }
        }
    }

    #[test]
    fn max_error_calculation() {
        let (_, shards) = DistributedCounter::new(8);
        let expected_error = FLUSH_THRESHOLD / 2 * 8;

        assert_eq!(shards[0].max_error(), expected_error);
    }

    #[test]
    fn concurrent_increments() {
        let (counter, shards) = DistributedCounter::new(4);

        std::thread::scope(|s| {
            for shard in &shards {
                let shard = Arc::clone(shard);
                s.spawn(move || {
                    for _ in 0..1000 {
                        shard.increment();
                    }
                });
            }
        });

        assert_eq!(counter.exact_value(), 4000);
    }

    #[test]
    fn flush_on_drop() {
        let global = Arc::new(AtomicU64::new(0));
        {
            let shard = CounterShard {
                local: AtomicU64::new(100),
                global: Arc::clone(&global),
                max_error: 0,
            };
            // shard drops here
            drop(shard);
        }
        assert_eq!(global.load(Ordering::Relaxed), 100);
    }
}
