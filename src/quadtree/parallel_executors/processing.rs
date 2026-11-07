//! Processing payload shared by an active owner, dependency pushers and notifiers.

use smallvec::SmallVec;
use std::{cell::UnsafeCell, mem, sync::atomic::AtomicU16};

pub(super) struct ProcessingData<Work, Dep> {
    work: UnsafeCell<Work>,
    pub(super) waiting_cnt: AtomicU16,
    dependents: UnsafeCell<SmallVec<[Dep; 2]>>,
}

// SAFETY: Work and dependents have separate synchronization domains. Their only
// mutable accessors require the owner bit or dependents lock respectively;
// waiting_cnt is atomic. Neither domain ever borrows the whole payload mutably.
unsafe impl<Work: Send, Dep: Send> Sync for ProcessingData<Work, Dep> {}

pub(super) struct ActiveWork<'a, Work> {
    pub(super) work: &'a mut Work,
    pub(super) waiting_cnt: &'a AtomicU16,
}

impl<Work: Default, Dep> ProcessingData<Work, Dep> {
    pub(super) fn new(dependents: SmallVec<[Dep; 2]>) -> Self {
        Self {
            work: UnsafeCell::new(Work::default()),
            waiting_cnt: AtomicU16::new(0),
            dependents: UnsafeCell::new(dependents),
        }
    }
}

impl<Work, Dep> ProcessingData<Work, Dep> {
    /// # Safety
    /// The caller holds ACTIVE for this payload until the returned view expires.
    /// No other owner view may coexist. Pushers and notifiers may still run.
    pub(super) unsafe fn active_work(&self) -> ActiveWork<'_, Work> {
        ActiveWork {
            work: unsafe { &mut *self.work.get() },
            waiting_cnt: &self.waiting_cnt,
        }
    }

    /// # Safety
    /// Every worker accessing this payload has joined; no owner or pusher may run.
    pub(super) unsafe fn paused_work(&self) -> &Work {
        unsafe { &*self.work.get() }
    }

    /// # Safety
    /// The caller holds DEPS_LOCK and the payload is PENDING or ACTIVE.
    pub(super) unsafe fn push_dependent(&self, dependent: Dep) {
        unsafe { &mut *self.dependents.get() }.push(dependent);
    }

    /// # Safety
    /// The caller holds the PROCESSING finish barrier; no pusher can access the list.
    pub(super) unsafe fn take_dependents(&self) -> SmallVec<[Dep; 2]> {
        mem::take(unsafe { &mut *self.dependents.get() })
    }
}

#[cfg(test)]
mod tests;
