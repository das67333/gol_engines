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
mod tests {
    use super::*;
    use crossbeam::deque::{Steal, Stealer, Worker};
    use std::{
        sync::mpsc,
        thread,
        time::{Duration, Instant},
    };

    fn scan<T>(queue: &Stealer<T>) -> Search<T> {
        loop {
            match queue.steal() {
                Steal::Success(task) => return Search::Work(task),
                Steal::Empty => return Search::Empty,
                Steal::Retry => {}
            }
        }
    }

    fn wait_for_sleepers(parking: &Parking, count: usize) {
        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let state = parking.state.lock().unwrap();
            assert!(state.sleepers.is_empty() || state.captain.is_some());
            assert!(!state.sleepers.iter().any(|id| Some(*id) == state.captain));
            if state.sleepers.len() == count {
                return;
            }
            drop(state);
            if Instant::now() >= deadline {
                parking.stop();
                panic!("workers did not register");
            }
            thread::yield_now();
        }
    }

    #[test]
    fn queued_work_needs_no_producer_notification() {
        let (parking, parkers) = Parking::new(8);
        let queue = Worker::new_lifo();
        let (sent, received) = mpsc::channel();
        thread::scope(|scope| {
            for (worker, parker) in parkers.into_iter().enumerate() {
                let parking = &parking;
                let queue = queue.stealer();
                let sent = sent.clone();
                scope.spawn(move || {
                    sent.send(parking.search(worker, &parker, || scan(&queue)))
                        .unwrap();
                });
            }
            wait_for_sleepers(&parking, 7);
            for task in 0..8 {
                queue.push(task);
            }
            let results: Vec<_> = (0..8)
                .map(|_| received.recv_timeout(Duration::from_secs(5)))
                .collect();
            parking.stop();
            let mut tasks: Vec<_> = results.into_iter().map(|r| r.unwrap().unwrap()).collect();
            tasks.sort_unstable();
            assert_eq!(tasks, (0..8).collect::<Vec<_>>());
        });
    }

    #[test]
    fn delayed_captain_hands_off_before_returning_work() {
        let (parking, mut parkers) = Parking::new(4);
        let queue = Worker::new_lifo();
        let (entered, scanning) = mpsc::channel();
        let (resume, resumed) = mpsc::channel();
        let (sent, received) = mpsc::channel();
        thread::scope(|scope| {
            let parking = &parking;
            let parker = parkers.remove(0);
            let stealer = queue.stealer();
            let sent0 = sent.clone();
            scope.spawn(move || {
                let mut first = true;
                let result = parking.search(0, &parker, || {
                    if first {
                        first = false;
                        entered.send(()).unwrap();
                        resumed.recv_timeout(Duration::from_secs(5)).unwrap();
                    }
                    scan(&stealer)
                });
                sent0.send(result).unwrap();
            });
            scanning.recv_timeout(Duration::from_secs(5)).unwrap();
            for (index, parker) in parkers.into_iter().enumerate() {
                let stealer = queue.stealer();
                let sent = sent.clone();
                scope.spawn(move || {
                    sent.send(parking.search(index + 1, &parker, || scan(&stealer)))
                        .unwrap();
                });
            }
            wait_for_sleepers(parking, 3);
            for task in 0..4 {
                queue.push(task);
            }
            resume.send(()).unwrap();
            let results: Vec<_> = (0..4)
                .map(|_| received.recv_timeout(Duration::from_secs(5)))
                .collect();
            parking.stop();
            assert!(results.into_iter().all(|r| r.unwrap().is_some()));
        });
    }

    #[test]
    fn idle_arrival_claims_an_unowned_captain() {
        let (parking, mut parkers) = Parking::new(1);
        let parker = parkers.pop().unwrap();
        for task in 0..3 {
            assert_eq!(
                parking.search(0, &parker, || Search::Work(task)),
                Some(task)
            );
            assert_eq!(parking.state.lock().unwrap().captain, None);
        }
        parking.stop();
    }

    #[test]
    fn stale_token_does_not_duplicate_registration() {
        let (parking, mut parkers) = Parking::new(2);
        // The test thread stands in for a delayed live captain.
        parking.state.lock().unwrap().captain = Some(0);
        let parker = parkers.pop().unwrap();
        parker.unparker().unpark();
        let (sent, received) = mpsc::channel();
        thread::scope(|scope| {
            let parking = &parking;
            scope.spawn(move || {
                let result: Option<()> = parking.search(1, &parker, || Search::Empty);
                sent.send(result).unwrap();
            });
            wait_for_sleepers(parking, 1);
            parking.stop();
            let result = received.recv_timeout(Duration::from_secs(5));
            assert_eq!(result.unwrap(), None);
        });
    }

    #[test]
    fn stop_races_arrival_and_captain_scanning() {
        for _ in 0..100 {
            let (parking, parkers) = Parking::new(4);
            let (sent, received) = mpsc::channel();
            thread::scope(|scope| {
                for (worker, parker) in parkers.into_iter().enumerate() {
                    let parking = &parking;
                    let sent = sent.clone();
                    scope.spawn(move || {
                        let result: Option<()> = parking.search(worker, &parker, || Search::Empty);
                        sent.send(result).unwrap();
                    });
                }
                parking.stop();
                for _ in 0..4 {
                    assert_eq!(received.recv_timeout(Duration::from_secs(5)).unwrap(), None);
                }
            });
        }
    }

    #[test]
    fn captain_panic_guard_wakes_parked_workers() {
        let (parking, mut parkers) = Parking::new(2);
        parking.state.lock().unwrap().captain = Some(0);
        let (sent, received) = mpsc::channel();
        thread::scope(|scope| {
            let parking = &parking;
            let peer = parkers.pop().unwrap();
            scope.spawn(move || {
                let result: Option<()> = parking.search(1, &peer, || Search::Empty);
                sent.send(result).unwrap();
            });
            wait_for_sleepers(parking, 1);
            let captain = parkers.pop().unwrap();
            let panicked = scope
                .spawn(move || {
                    let _guard = parking.stop_on_exit();
                    let _: Option<()> =
                        parking.search(0, &captain, || panic!("simulated captain panic"));
                })
                .join();
            let peer = received.recv_timeout(Duration::from_secs(5));
            parking.stop();
            assert!(panicked.is_err());
            assert_eq!(peer.unwrap(), None);
        });
    }
}
