//! One idle search captain keeps publication off the producer hot path.
use crossbeam::{sync::Parker, utils::CachePadded};
use std::sync::{
    Mutex,
    atomic::{AtomicBool, Ordering},
};

const PARK_SPINS: usize = 1024;

pub(super) enum Search<T> {
    Work(T),
    Empty,
    Stop,
}

#[derive(Default)]
struct State {
    captain: Option<usize>,
    sleepers: Vec<usize>,
}

pub(super) struct Parking {
    state: Mutex<State>,
    stopped: AtomicBool,
    unparks: Vec<crossbeam::sync::Unparker>,
    wake_hints: Vec<CachePadded<AtomicBool>>,
}

impl Parking {
    pub(super) fn new(workers: usize) -> (Self, Vec<Parker>) {
        let parkers: Vec<_> = (0..workers).map(|_| Parker::new()).collect();
        let unparks = parkers.iter().map(|p| p.unparker().clone()).collect();
        (
            Self {
                state: Mutex::new(State::default()),
                stopped: AtomicBool::new(false),
                unparks,
                wake_hints: (0..workers)
                    .map(|_| CachePadded::new(AtomicBool::new(false)))
                    .collect(),
            },
            parkers,
        )
    }

    /// Only the captain scans in this wait loop. Other idle workers keep one registration
    /// and recheck the captain reservation after each wake.
    pub(super) fn search<T>(
        &self,
        worker: usize,
        parker: &Parker,
        mut scan: impl FnMut() -> Search<T>,
    ) -> Option<T> {
        loop {
            let mut state = self.state.lock().unwrap();
            if self.stopped.load(Ordering::Acquire) {
                return None;
            }
            if let Some(index) = state.sleepers.iter().position(|&id| id == worker) {
                state.sleepers.swap_remove(index);
            }
            match state.captain {
                None => state.captain = Some(worker),
                Some(captain) if captain == worker => {}
                Some(_) => {
                    self.wake_hints[worker].store(false, Ordering::Relaxed);
                    state.sleepers.push(worker);
                    drop(state);
                    self.park(worker, parker);
                    continue;
                }
            }
            drop(state);
            loop {
                if self.stopped.load(Ordering::Acquire) {
                    return None;
                }
                match scan() {
                    Search::Work(task) => {
                        let mut state = self.state.lock().unwrap();
                        if self.stopped.load(Ordering::Acquire) {
                            return None;
                        }
                        // Transfer responsibility before becoming a producer.
                        // If no sleeper remains, the next idle arrival claims it.
                        state.captain = state.sleepers.pop();
                        let captain = state.captain;
                        drop(state);
                        if let Some(captain) = captain {
                            self.unpark(captain);
                        }
                        return Some(task);
                    }
                    Search::Empty => std::hint::spin_loop(),
                    Search::Stop => {
                        self.stop();
                        return None;
                    }
                }
            }
        }
    }

    /// A short spin can consume a prompt handoff without entering the kernel.
    /// The hint does not grant the role; the mutex still protects that decision.
    fn park(&self, worker: usize, parker: &Parker) {
        for _ in 0..PARK_SPINS {
            if self.wake_hints[worker].load(Ordering::Acquire) {
                break;
            }
            std::hint::spin_loop();
        }
        parker.park();
    }

    fn unpark(&self, worker: usize) {
        self.wake_hints[worker].store(true, Ordering::Release);
        self.unparks[worker].unpark();
    }

    fn stop(&self) {
        // Only one worker performs the broadcast, including during unwinding.
        if self.stopped.swap(true, Ordering::AcqRel) {
            return;
        }
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        state.captain = None;
        state.sleepers.clear();
        // Wake every worker, including a captain awaiting its reserved wake.
        for worker in 0..self.unparks.len() {
            self.unpark(worker);
        }
    }

    pub(super) fn stop_on_exit(&self) -> impl Drop + '_ {
        struct Guard<'a>(&'a Parking);
        impl Drop for Guard<'_> {
            fn drop(&mut self) {
                self.0.stop();
            }
        }
        Guard(self)
    }
}

#[cfg(test)]
mod tests;
