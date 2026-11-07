//! One idle search captain keeps publication off the producer hot path.
use crossbeam::sync::Parker;
use std::sync::{
    Mutex,
    atomic::{AtomicBool, Ordering},
};

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
                    state.sleepers.push(worker);
                    drop(state);
                    parker.park();
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
                        if let Some(captain) = state.captain {
                            self.unparks[captain].unpark();
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

    fn stop(&self) {
        // Only one worker performs the broadcast, including during unwinding.
        if self.stopped.swap(true, Ordering::AcqRel) {
            return;
        }
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        state.captain = None;
        state.sleepers.clear();
        // Wake every worker, including a captain awaiting its reserved wake.
        for unparker in &self.unparks {
            unparker.unpark();
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
