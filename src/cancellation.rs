use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};

/// Requests cancellation of an engine update without changing the last completed state.
#[derive(Clone, Default)]
pub struct CancellationToken(Arc<AtomicBool>);

impl CancellationToken {
    /// Ask the engine to stop at a safe point. Cleanup may take additional time.
    pub fn cancel(&self) {
        self.0.store(true, Ordering::Relaxed);
    }

    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }

    /// Allow another update. Call only after the cancelled update has returned.
    pub fn reset(&self) {
        self.0.store(false, Ordering::Relaxed);
    }
}

/// An update was cancelled; the engine still contains its pre-update state.
#[derive(Debug)]
pub struct UpdateCancelled;

impl std::fmt::Display for UpdateCancelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Update cancelled")
    }
}

impl std::error::Error for UpdateCancelled {}
