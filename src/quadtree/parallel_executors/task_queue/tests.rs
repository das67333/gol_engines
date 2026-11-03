use super::*;

impl TaskWord for usize {
    fn into_word(self) -> u64 {
        self as u64
    }
    fn from_word(word: u64) -> Self {
        word as usize
    }
}

use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn local_and_foreign_order_and_single_task_transfer() {
    let source = TaskQueue::<usize>::new(8);
    let destination = TaskQueue::new(8);
    for value in 0..4 {
        source.push(value);
    }
    let stealer = source.stealer();
    assert_eq!(source.pop(), Some(3));
    assert_eq!(destination.steal_from(&stealer), Steal::Success(0));
    assert_eq!(destination.pop(), None);
    assert_eq!(source.steal_from(&stealer), Steal::Success(2));
    assert_eq!(source.pop(), Some(1));
    assert_eq!(destination.steal_from(&stealer), Steal::Empty);
}

#[test]
fn growth_preserves_local_and_foreign_order() {
    let queue = TaskQueue::<usize>::new(2);
    let stealer = queue.stealer();
    for value in 0..1000 {
        queue.push(value);
    }
    for value in 0..500 {
        assert_eq!(stealer.steal(), Steal::Success(value));
    }
    for value in (500..1000).rev() {
        assert_eq!(queue.pop(), Some(value));
    }
    assert_eq!(queue.pop(), None);
}

#[test]
fn owner_and_thieves_deliver_each_task_once() {
    const TASKS: usize = 2048;
    let source = TaskQueue::new(2);
    let seen: Vec<_> = (0..TASKS).map(|_| AtomicUsize::new(0)).collect();
    let received = AtomicUsize::new(0);
    for value in 0..TASKS {
        source.push(value);
    }
    std::thread::scope(|scope| {
        for _ in 0..4 {
            let victim = source.stealer();
            let seen = &seen;
            let received = &received;
            scope.spawn(move || {
                let destination = TaskQueue::new(2);
                while received.load(Ordering::Relaxed) != TASKS {
                    if let Steal::Success(value) = destination.steal_from(&victim) {
                        seen[value].fetch_add(1, Ordering::Relaxed);
                        received.fetch_add(1, Ordering::Relaxed);
                    }
                }
            });
        }
        while let Some(value) = source.pop() {
            seen[value].fetch_add(1, Ordering::Relaxed);
            received.fetch_add(1, Ordering::Relaxed);
        }
    });
    assert_eq!(received.load(Ordering::Relaxed), TASKS);
    assert!(seen.iter().all(|count| count.load(Ordering::Relaxed) == 1));
}

#[test]
fn concurrent_delivery_remains_exact_across_buffer_reuse() {
    const TASKS: usize = 8192;
    const BATCH: usize = 64;
    let source = TaskQueue::<usize>::new(2);
    let seen: Vec<_> = (0..TASKS).map(|_| AtomicUsize::new(0)).collect();
    let received = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for _ in 0..4 {
            let victim = source.stealer();
            let seen = &seen;
            let received = &received;
            scope.spawn(move || {
                let destination = TaskQueue::new(2);
                while received.load(Ordering::Relaxed) != TASKS {
                    if let Steal::Success(value) = destination.steal_from(&victim) {
                        seen[value].fetch_add(1, Ordering::Relaxed);
                        received.fetch_add(1, Ordering::Relaxed);
                    }
                }
            });
        }
        for first in (0..TASKS).step_by(BATCH) {
            for value in first..first + BATCH {
                source.push(value);
            }
            while let Some(value) = source.pop() {
                seen[value].fetch_add(1, Ordering::Relaxed);
                received.fetch_add(1, Ordering::Relaxed);
            }
        }
    });
    assert_eq!(received.load(Ordering::Relaxed), TASKS);
    assert!(seen.iter().all(|count| count.load(Ordering::Relaxed) == 1));
}

#[test]
fn a_stealer_keeps_queued_tasks_alive_after_the_owner_exits() {
    let queue = TaskQueue::<usize>::new(4);
    queue.push(17);
    queue.push(23);
    let stealer = queue.stealer();
    drop(queue);
    assert_eq!(stealer.steal(), Steal::Success(17));
    assert_eq!(stealer.steal(), Steal::Success(23));
    assert_eq!(stealer.steal(), Steal::Empty);
}
