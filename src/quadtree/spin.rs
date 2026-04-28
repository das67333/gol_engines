//! Adaptive spin-wait helper.
//!
//! Replaces bare `hint::spin_loop()` busy-waits in the engine's hot
//! synchronization paths. The first [`YIELD_THRESHOLD`] iterations issue a
//! cheap CPU pause hint (so brief, uncontended waits stay fast); after that
//! every iteration calls [`thread::yield_now`] so the OS scheduler can run
//! the holder of the contended resource.
//!
//! This matters under thread oversubscription (more software threads than
//! hardware cores). A preempted holder of a spinlock-style bit can stall
//! every spinning waiter for an entire scheduling quantum, multiplied by
//! the number of waiters. Switching to [`thread::yield_now`] after a short
//! optimistic phase bounds the worst case to scheduler latency instead.

use std::{hint, thread};

/// Spin iterations to perform with `hint::spin_loop()` before falling back
/// to `thread::yield_now()`. Picked so that the common, uncontended case
/// (a handful of pauses while another core publishes a value) never yields,
/// while degenerate cases recover quickly.
const YIELD_THRESHOLD: u64 = 1024;

/// Counter-backed adaptive spinner. See module docs.
#[derive(Default)]
pub(super) struct Spinner {
    count: u64,
}

impl Spinner {
    pub(super) const fn new() -> Self {
        Self { count: 0 }
    }

    /// Pause for one spin iteration. Below [`YIELD_THRESHOLD`] this is a
    /// CPU pause hint; once the threshold is exceeded each call yields the
    /// remainder of the thread's quantum to the OS scheduler.
    #[inline]
    pub(super) fn spin(&mut self) {
        self.count += 1;
        if self.count <= YIELD_THRESHOLD {
            hint::spin_loop();
        } else {
            thread::yield_now();
        }
    }

    /// Total number of [`Self::spin`] calls performed. Reported as a spin
    /// metric at the end of each waiting loop.
    #[inline]
    pub(super) fn count(&self) -> u64 {
        self.count
    }
}
