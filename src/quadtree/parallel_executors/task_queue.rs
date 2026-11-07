//! Owner-LIFO / thief-FIFO task queue with atomic task words.
//! Buffers grow geometrically and remain alive until the final queue handle drops.
//! This avoids per-steal reclamation guards and bounds retained buffer storage by
//! twice the largest buffer. The index protocol follows Crossbeam's Chase-Lev deque.

// Index protocol adapted from crossbeam-deque 0.8.6.
// Copyright (c) 2019 The Crossbeam Project Developers.
// MIT license: LICENSES/crossbeam-deque.txt.

use crossbeam::{deque::Steal, utils::CachePadded};
use std::{
    cell::Cell,
    marker::PhantomData,
    sync::{
        Arc, OnceLock,
        atomic::{self, AtomicIsize, AtomicU64, AtomicUsize, Ordering},
    },
};

/// A task encoded losslessly in one atomic slot.
pub(super) trait TaskWord: Copy + Send + Sync {
    fn into_word(self) -> u64;
    fn from_word(word: u64) -> Self;
}

struct Inner {
    front: AtomicIsize,
    back: AtomicIsize,
    current: AtomicUsize,
    buffers: CachePadded<[OnceLock<Box<[AtomicU64]>>; usize::BITS as usize]>,
}

fn slot(buffer: &[AtomicU64], index: isize) -> &AtomicU64 {
    &buffer[index as usize & (buffer.len() - 1)]
}

impl Inner {
    fn buffer(&self) -> &[AtomicU64] {
        self.buffers[self.current.load(Ordering::Acquire)]
            .get()
            .unwrap()
    }

    fn grow(&self, front: isize, back: isize) -> &[AtomicU64] {
        let previous = self.buffer();
        let capacity = previous
            .len()
            .checked_mul(2)
            .expect("task queue capacity overflow");
        let buffer: Box<[AtomicU64]> = (0..capacity).map(|_| AtomicU64::new(0)).collect();
        for offset in 0..back.wrapping_sub(front) {
            let index = front.wrapping_add(offset);
            slot(&buffer, index).store(
                slot(previous, index).load(Ordering::Relaxed),
                Ordering::Relaxed,
            );
        }
        let next = self.current.load(Ordering::Relaxed) + 1;
        assert!(self.buffers[next].set(buffer).is_ok());
        self.current.store(next, Ordering::Release);
        self.buffers[next].get().unwrap()
    }
}

pub(super) struct TaskQueue<T: TaskWord> {
    inner: Arc<CachePadded<Inner>>,
    // The worker is movable, but owner operations cannot be shared between threads.
    marker: PhantomData<Cell<T>>,
}

pub(super) struct TaskStealer<T: TaskWord> {
    inner: Arc<CachePadded<Inner>>,
    marker: PhantomData<T>,
}

impl<T: TaskWord> TaskQueue<T> {
    pub(super) fn new(capacity: usize) -> Self {
        assert!(capacity.is_power_of_two());
        let buffers = std::array::from_fn(|_| OnceLock::new());
        let buffer: Box<[AtomicU64]> = (0..capacity).map(|_| AtomicU64::new(0)).collect();
        assert!(buffers[0].set(buffer).is_ok());
        Self {
            inner: Arc::new(CachePadded::new(Inner {
                front: AtomicIsize::new(0),
                back: AtomicIsize::new(0),
                current: AtomicUsize::new(0),
                buffers: CachePadded::new(buffers),
            })),
            marker: PhantomData,
        }
    }

    pub(super) fn push(&self, task: T) {
        let back = self.inner.back.load(Ordering::Relaxed);
        let front = self.inner.front.load(Ordering::Acquire);
        let mut buffer = self.inner.buffer();
        if back.wrapping_sub(front) >= buffer.len() as isize {
            buffer = self.inner.grow(front, back);
        }
        slot(buffer, back).store(task.into_word(), Ordering::Relaxed);
        atomic::fence(Ordering::Release);
        self.inner
            .back
            .store(back.wrapping_add(1), Ordering::Release);
    }

    pub(super) fn pop(&self) -> Option<T> {
        let back = self.inner.back.load(Ordering::Relaxed);
        let front = self.inner.front.load(Ordering::Relaxed);
        if back.wrapping_sub(front) <= 0 {
            return None;
        }
        let back = back.wrapping_sub(1);
        self.inner.back.store(back, Ordering::Relaxed);
        atomic::fence(Ordering::SeqCst);
        let front = self.inner.front.load(Ordering::Relaxed);
        let remaining = back.wrapping_sub(front);
        if remaining < 0 {
            self.inner
                .back
                .store(back.wrapping_add(1), Ordering::Relaxed);
            return None;
        }
        let word = slot(self.inner.buffer(), back).load(Ordering::Relaxed);
        if remaining == 0 {
            let claimed = self
                .inner
                .front
                .compare_exchange(
                    front,
                    front.wrapping_add(1),
                    Ordering::SeqCst,
                    Ordering::Relaxed,
                )
                .is_ok();
            self.inner
                .back
                .store(back.wrapping_add(1), Ordering::Relaxed);
            if !claimed {
                return None;
            }
        }
        Some(T::from_word(word))
    }

    pub(super) fn stealer(&self) -> TaskStealer<T> {
        TaskStealer {
            inner: self.inner.clone(),
            marker: PhantomData,
        }
    }

    pub(super) fn steal_from(&self, victim: &TaskStealer<T>) -> Steal<T> {
        if Arc::ptr_eq(&self.inner, &victim.inner) {
            return self.pop().map_or(Steal::Empty, Steal::Success);
        }
        victim.steal()
    }
}

impl<T: TaskWord> TaskStealer<T> {
    fn steal(&self) -> Steal<T> {
        let front = self.inner.front.load(Ordering::Acquire);
        atomic::fence(Ordering::SeqCst);
        let back = self.inner.back.load(Ordering::Acquire);
        if back.wrapping_sub(front) <= 0 {
            return Steal::Empty;
        }
        // If back includes a post-growth push, its Acquire load also observes
        // the earlier buffer publication. An older buffer stays valid otherwise.
        let word = slot(self.inner.buffer(), front).load(Ordering::Relaxed);
        if self
            .inner
            .front
            .compare_exchange(
                front,
                front.wrapping_add(1),
                Ordering::SeqCst,
                Ordering::Relaxed,
            )
            .is_err()
        {
            return Steal::Retry;
        }
        Steal::Success(T::from_word(word))
    }
}

#[cfg(test)]
mod tests;
