//! # Lock-free "close-once" dependents stack
//!
//! A single-publisher-multi-pusher linked list used by the parallel executors
//! to track nodes waiting for a computation to finish. Replaces the previous
//! `SmallVec<[_; 2]>` dependents list that was protected by the `PROCESSING`
//! status bit, removing that contention point entirely.
//!
//! ## Lifecycle
//!
//! 1. Pushers (other tasks that depend on this node) call [`DepHead::push`].
//! 2. Exactly once, the owning task calls [`DepHead::close`] to swap the head
//!    with a sentinel and obtain every dependent that was ever registered.
//! 3. After [`DepHead::close`], further pushes fail with [`PushResult::Closed`];
//!    the caller interprets this as "the dependency is already done".
//!
//! ## Encoding
//!
//! The head is an `AtomicUsize` with four possible values:
//!
//! | Value                  | Meaning                                 |
//! |------------------------|-----------------------------------------|
//! | `0`                    | Empty (no dependents)                   |
//! | `(idx << 1) \| 1`      | Inline single [`Idx`] (no allocation)   |
//! | `ptr` (bit 0 == 0, ≠0) | Pointer to head of [`DepCell`] list     |
//! | `usize::MAX`           | Closed (sentinel); published once       |
//!
//! The inline-Idx variant avoids heap allocation for the overwhelmingly
//! common case of a node having exactly one dependent.
//!
//! ## ABA safety
//!
//! Standard Treiber-stack ABA issues don't apply here because:
//! - The stack is push-only until [`close`].
//! - [`close`] performs a single atomic `swap` to the closed sentinel.
//! - After `close`, no operation writes anything other than the sentinel.
//! - Cells are freed only during drain, after `close` has run, while no other
//!   thread holds a pointer to them (pushers only CAS the *head*; they never
//!   dereference cells).

use std::{
    ptr,
    sync::atomic::{AtomicUsize, Ordering},
};

use super::hashtable::Idx;

/// Heap-allocated cell holding a single dependent's [`Idx`] and a link to the
/// next cell on the stack.
pub(super) struct DepCell {
    pub(super) parent_idx: Idx,
    pub(super) next: *mut DepCell,
}

// SAFETY: Cells are moved between threads only by the owner at `close()`
// time; all concurrent operations are through the atomic head.
unsafe impl Send for DepCell {}
unsafe impl Sync for DepCell {}

/// Sentinel value published by [`DepHead::close`]. Distinct from every valid
/// encoding (pointers are not `usize::MAX`, inline Idx fits in 33 bits on
/// 64-bit targets).
const CLOSED_SENTINEL: usize = usize::MAX;

#[inline]
const fn encode_inline(idx: Idx) -> usize {
    ((idx as usize) << 1) | 1
}

/// Decoded state of a [`DepHead`].
pub(super) enum DepState {
    /// No dependents were ever pushed (or stack was empty at `close` time).
    Empty,
    /// Exactly one dependent; stored inline without allocation.
    InlineIdx(Idx),
    /// Pointer to a non-empty singly linked list of [`DepCell`].
    Stack(*mut DepCell),
    /// The stack was closed; no further pushes allowed.
    Closed,
}

#[inline]
fn decode(value: usize) -> DepState {
    if value == 0 {
        DepState::Empty
    } else if value == CLOSED_SENTINEL {
        DepState::Closed
    } else if value & 1 != 0 {
        DepState::InlineIdx((value >> 1) as Idx)
    } else {
        DepState::Stack(value as *mut DepCell)
    }
}

/// Outcome of [`DepHead::push`].
pub(super) enum PushResult {
    /// The dependent was successfully registered.
    Pushed,
    /// The stack was already closed; the caller should treat the dependency
    /// as already finished.
    Closed,
}

/// Lock-free close-once stack head.
#[derive(Debug, Default)]
pub(super) struct DepHead(AtomicUsize);

impl DepHead {
    /// Push `parent_idx` onto the stack.
    ///
    /// Returns [`PushResult::Closed`] if [`close`] has already been called.
    pub(super) fn push(&self, parent_idx: Idx) -> PushResult {
        // Fast path: empty -> inline. No allocation. Satisfies >99% of nodes
        // whose dependents count never exceeds one.
        let inline_val = encode_inline(parent_idx);
        if self
            .0
            .compare_exchange(0, inline_val, Ordering::Release, Ordering::Acquire)
            .is_ok()
        {
            return PushResult::Pushed;
        }
        self.push_slow(parent_idx)
    }

    #[cold]
    fn push_slow(&self, parent_idx: Idx) -> PushResult {
        loop {
            let cur = self.0.load(Ordering::Acquire);
            match decode(cur) {
                DepState::Closed => return PushResult::Closed,
                DepState::Empty => {
                    let inline_val = encode_inline(parent_idx);
                    if self
                        .0
                        .compare_exchange_weak(
                            0,
                            inline_val,
                            Ordering::Release,
                            Ordering::Acquire,
                        )
                        .is_ok()
                    {
                        return PushResult::Pushed;
                    }
                }
                DepState::InlineIdx(existing) => {
                    // Promote inline -> stack. Allocate a cell for the existing
                    // inline idx plus a cell for the new idx, linked together.
                    let cell_existing = Box::into_raw(Box::new(DepCell {
                        parent_idx: existing,
                        next: ptr::null_mut(),
                    }));
                    let cell_new = Box::into_raw(Box::new(DepCell {
                        parent_idx,
                        next: cell_existing,
                    }));
                    if self
                        .0
                        .compare_exchange_weak(
                            cur,
                            cell_new as usize,
                            Ordering::Release,
                            Ordering::Acquire,
                        )
                        .is_ok()
                    {
                        return PushResult::Pushed;
                    }
                    // CAS lost; free speculatively-allocated cells and retry.
                    unsafe {
                        drop(Box::from_raw(cell_new));
                        drop(Box::from_raw(cell_existing));
                    }
                }
                DepState::Stack(existing_ptr) => {
                    let cell_new = Box::into_raw(Box::new(DepCell {
                        parent_idx,
                        next: existing_ptr,
                    }));
                    if self
                        .0
                        .compare_exchange_weak(
                            cur,
                            cell_new as usize,
                            Ordering::Release,
                            Ordering::Acquire,
                        )
                        .is_ok()
                    {
                        return PushResult::Pushed;
                    }
                    unsafe { drop(Box::from_raw(cell_new)) };
                }
            }
        }
    }

    /// Close the stack and return its current contents.
    ///
    /// After this call, every [`push`] returns [`PushResult::Closed`]. The
    /// returned [`DepState`] must be drained by the caller (via [`drain`])
    /// to free heap-allocated cells and to decrement dependents' counters.
    ///
    /// Must be called at most once in the lifetime of a stack; subsequent
    /// calls return [`DepState::Closed`].
    pub(super) fn close(&self) -> DepState {
        let old = self.0.swap(CLOSED_SENTINEL, Ordering::AcqRel);
        decode(old)
    }
}

/// Walk a chain returned by [`DepHead::close`], invoking `f(idx)` for each
/// dependent and freeing every heap-allocated [`DepCell`].
///
/// Safe to call with any [`DepState`]. No-ops on `Empty` and `Closed`.
pub(super) fn drain<F: FnMut(Idx)>(state: DepState, mut f: F) {
    match state {
        DepState::Empty | DepState::Closed => {}
        DepState::InlineIdx(idx) => f(idx),
        DepState::Stack(head) => {
            let mut cur = head;
            while !cur.is_null() {
                // SAFETY: `cur` was published by a successful CAS and removed
                // from the stack by the caller's `close()`, so no other thread
                // can observe it. We own it and free it here.
                let cell = unsafe { Box::from_raw(cur) };
                f(cell.parent_idx);
                cur = cell.next;
            }
        }
    }
}
