//! # Parallel Hashlife Executor
//!
//! This module implements a work-stealing parallel executor for the Hashlife algorithm.
//!
//! ## Architecture
//!
//! The executor uses thread-local LIFO queues with work-stealing for load balancing:
//! - Each thread has its own `Worker<Task>` queue
//! - When a thread runs out of work, it steals from other threads via `Stealer`
//! - No global queue is used - all tasks go directly to thread-local queues
//!
//! ## Status State Machine
//!
//! Each node progresses through these states during parallel processing:
//!
//! ```text
//!     ┌──────────────────────┐
//!     │    NOT_STARTED (0)   │ ◄── Initial state
//!     └──────────┬───────────┘
//!                │
//!                │ CAS(NOT_STARTED → PROCESSING)
//!                │ First thread claims the node
//!                ▼
//!     ┌──────────────────────┐                      ┌──────────────────────┐
//!     │    PROCESSING (1)    │ ◄─┐                  │    FINISHED (3)      │
//!     └──────────┬───────────┘   │                  └──────────────────────┘
//!                │               │                            ▲
//!                ├───────────────┼────────────────────────────┘
//!                │               │  store(FINISHED) when computation completes
//!                │               │
//!                │ store(PENDING)│ CAS(PENDING → PROCESSING)
//!                │ when waiting  │ when owner resumes work
//!                │ for deps      │
//!                ▼               │
//!     ┌──────────────────────┐   │
//!     │     PENDING (2)      │ ──┘
//!     └──────────────────────┘
//! ```
//!
//! Key transitions:
//! - `NOT_STARTED → PROCESSING`: Thread claims node for processing.
//! - `PROCESSING → PENDING`: Node needs to wait for dependencies.
//! - `PENDING → PROCESSING`: Owner thread resumes work on this node.
//! - `PROCESSING → FINISHED`: Computation complete, result cached.
//!
//! ## Concurrency model
//!
//! The `PROCESSING` status is the owner's exclusive lock for the
//! `ProcessingData` box (the scratch arrays `arr`, `mask9_waiting`,
//! `mask4_waiting`). It is only ever acquired by the thread that is about to
//! execute `update_node` on this particular node.
//!
//! Cross-thread coordination — dependent registration and dependency-
//! completion notification — runs entirely lock-free:
//!
//! - **Dependent registration** uses the lock-free
//!   [`DepHead`](super::dep_stack::DepHead) close-once stack living on the
//!   node itself. Pushers never acquire `PROCESSING`.
//! - **Dependency-completion** decrements the dependent's
//!   `QuadTreeNode::waiting_cnt` (also on the node, permanent storage) via
//!   a plain `fetch_sub`. Notifiers never acquire `PROCESSING`.
//!
//! ## Bias protocol for `waiting_cnt`
//!
//! While the owner is scanning children inside `update_node`, it holds a
//! `+1` bias on its own `waiting_cnt`. This prevents a concurrent notifier
//! — one of the owner's dependencies finishing faster than the owner can
//! register the next dependency — from bringing `waiting_cnt` to zero and
//! re-enqueueing the node while the owner is still touching the
//! owner-private `ProcessingData`. The bias is released at the end of
//! `update_node`; if the release is the final decrement, the owner
//! self-re-enqueues.

use super::{
    LEAF_SIZE, LEAF_SIZE_LOG2, algorithm,
    dep_stack::{self, DepState, PushResult},
    hashlife::HashLifeEngine,
    hashtable::{Idx, NodeStore, NodeStoreRef},
    node::QuadTreeNode,
    sharded_statistics::*,
    status,
};
use crossbeam::deque::{Steal, Stealer, Worker};
use std::{
    hint,
    sync::atomic::{AtomicU8, Ordering},
    thread,
    time::Duration,
};

/// Temporary data allocated during node processing.
///
/// Heap-allocated when processing starts, freed when the node reaches
/// `FINISHED` state. Stored via pointer in the node's `cache` field.
///
/// These fields are **owner-private**: only the thread currently holding
/// `PROCESSING` on this node ever reads or writes them. `waiting_cnt` and
/// the dependents list live directly on the node (see
/// [`QuadTreeNode::waiting_cnt`] and
/// [`QuadTreeNode::dependents_head`](super::node::QuadTreeNode)) so that
/// they are safe to touch without locks.
#[derive(Default)]
struct ProcessingData {
    /// Intermediate child node results (up to 9 for overlapping, 4 for final stage).
    arr: [Idx; 9],
    /// Bitmask: bit `i` set if `arr[i]` (among first 9) is not yet computed.
    mask9_waiting: u32,
    /// Bitmask: bit `i` set if `arr[i]` (among first 4) is not yet computed.
    mask4_waiting: u32,
}

/// A unit of work representing a node to be processed.
struct Task {
    idx: Idx,
    size_log2: u32,
}

impl Task {
    fn new(idx: Idx, size_log2: u32) -> Self {
        Self { idx, size_log2 }
    }
}

pub(super) struct TaskFetcher<'a, T: Send, F: Fn() -> bool, C: Fn() -> bool> {
    thread_idx: usize,
    queue: &'a Worker<T>,
    stealers: &'a [Stealer<T>],
    finish_condition: F,
    cancel_condition: C,
    last_victim: usize,
    rng: rand_chacha::ChaCha8Rng,
}

impl<'a, T: Send, F: Fn() -> bool, C: Fn() -> bool> TaskFetcher<'a, T, F, C> {
    /// Number of tasks to steal at once when work-stealing.
    const STEAL_BATCH_SIZE: usize = 1;
    const INITIAL_WAIT_DURATION: Duration = Duration::from_micros(100);
    const MAX_WAIT_DURATION: Duration = Duration::from_millis(100);

    pub(super) fn new(
        thread_idx: usize,
        queue: &'a Worker<T>,
        stealers: &'a [Stealer<T>],
        finish_condition: F,
        cancel_condition: C,
    ) -> Self {
        Self {
            thread_idx,
            queue,
            stealers,
            finish_condition,
            cancel_condition,
            last_victim: 0,
            rng: <rand_chacha::ChaCha8Rng as rand::SeedableRng>::from_os_rng(),
        }
    }

    /// Fetch a task from local queue or steal from other threads.
    /// Records steal/last-victim stats via thread-local execution statistics.
    pub(super) fn fetch_task(&mut self) -> Option<T> {
        if (self.cancel_condition)() {
            return None;
        }

        // local queue
        if let Some(task) = self.queue.pop() {
            return Some(task);
        }

        if self.stealers.len() <= 1 {
            return None;
        }

        // repeat last successful steal
        let result = self.try_steal(self.last_victim);
        record_last_victim_steal(&result);
        if result.is_some() {
            return result;
        }

        let mut duration = Self::INITIAL_WAIT_DURATION;
        while !(self.finish_condition)() && !(self.cancel_condition)() {
            // power of two choices - choosing a longer queue
            let (i, j) = (self.generate_random_index(), self.generate_random_index());
            let (len_i, len_j) = (self.stealers[i].len(), self.stealers[j].len());
            let (victim_id, victim_len) = if len_i > len_j {
                (i, len_i)
            } else {
                (j, len_j)
            };
            if victim_len > 0
                && let Some(task) = self.try_steal(victim_id)
            {
                self.last_victim = victim_id;
                return Some(task);
            }

            thread::sleep(duration);
            duration = Self::MAX_WAIT_DURATION.min(duration * 2);
        }

        None
    }

    fn generate_random_index(&mut self) -> usize {
        use rand::Rng;
        // don't steal from yourself
        let mut i = self.rng.random_range(0..self.stealers.len() - 1);
        if i >= self.thread_idx {
            i += 1;
        }
        i
    }

    fn try_steal(&mut self, victim_id: usize) -> Option<T> {
        loop {
            let result = self.stealers[victim_id]
                .steal_batch_with_limit_and_pop(self.queue, Self::STEAL_BATCH_SIZE);
            record_steal(&result);
            match result {
                Steal::Success(task) => return Some(task),
                Steal::Empty => return None,
                Steal::Retry => continue,
            }
        }
    }
}

/// Parallel executor for Hashlife algorithm using work-stealing.
pub(super) struct HashLifeExecutor<'a, Meta: Default + Sync> {
    root: Idx,
    size_log2: u32,
    generations_log2: u32,
    mem: &'a NodeStore<Meta>,
}

impl<'a, Meta: Default + Sync> HashLifeExecutor<'a, Meta> {
    pub(super) fn new(base: &'a HashLifeEngine<Meta>) -> Self {
        Self {
            root: base.root,
            size_log2: base.size_log2,
            generations_log2: base.generations_per_update_log2.unwrap(),
            mem: &base.mem,
        }
    }

    pub(super) fn run(&self, num_threads: usize) -> Option<Idx> {
        // Create worker queues and stealers
        let mut queues = Vec::with_capacity(num_threads);
        let mut stealers = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let queue = Worker::new_lifo();
            let stealer = queue.stealer();
            queues.push(queue);
            stealers.push(stealer);
        }

        let root_node = self.mem.get(self.root);
        // Root has no parent, so it carries no initial dependent.
        let claimed = start_processing_node(root_node, None);
        assert!(claimed, "root must be in NOT_STARTED state");
        queues[0].push(Task::new(self.root, self.size_log2));

        let mut total_stats = ExecutionStatistics::new();
        thread::scope(|scope| {
            let mut handles = Vec::with_capacity(num_threads);
            for (thread_idx, queue) in queues.into_iter().enumerate() {
                let executor_thread = ExecutorThread {
                    root_node,
                    generations_log2: self.generations_log2,
                    mem: self.mem.create_ref(thread_idx),
                    thread_idx,
                    queue,
                    stealers: &stealers,
                };
                handles.push(scope.spawn(move || executor_thread.run()));
            }

            for handle in handles {
                total_stats.merge_from(&handle.join().unwrap());
            }
        });

        if self.mem.exceeds_load_factor() {
            return None;
        }

        assert!(is_finished(&self.mem.get(self.root).status));
        println!("Nodes count: {}", self.mem.len());
        println!("{total_stats}");

        Some(root_node.cache.get_value())
    }
}

struct ExecutorThread<'a, Meta: Default + Sync> {
    root_node: &'a QuadTreeNode<Meta>,
    generations_log2: u32,
    mem: NodeStoreRef<'a, Meta>,
    thread_idx: usize,
    queue: Worker<Task>,
    stealers: &'a [Stealer<Task>],
}

impl<'a, Meta: Default + Sync> ExecutorThread<'a, Meta> {
    fn run(&self) -> ExecutionStatistics {
        let mut fetcher = TaskFetcher::new(
            self.thread_idx,
            &self.queue,
            self.stealers,
            || is_finished(&self.root_node.status),
            || self.mem.exceeds_load_factor(),
        );
        set_current_execution_stats();

        while let Some(task) = fetcher.fetch_task() {
            let start = Ticks::now();
            self.process_task(task);
            record_task_duration(Ticks::now().elapsed_since(start));
        }

        take_current_execution_stats().unwrap()
    }

    /// Process a single task: compute the node's result or wait for dependencies.
    ///
    /// Flow:
    /// 1. Acquire PROCESSING status via `ProcessingGuard` (owner-exclusive).
    /// 2. Add owner bias (`waiting_cnt += 1`) — prevents concurrent notifiers
    ///    from racing us to zero during the scan.
    /// 3. Call `update_node` to compute result or identify dependencies.
    /// 4. If result ready: publish result, close dependents stack, mark
    ///    FINISHED, free `ProcessingData`, notify dependents.
    /// 5. If waiting: drop guard (back to PENDING), release bias; if that
    ///    brought `waiting_cnt` to zero (all deps already finished during
    ///    scan), self-re-enqueue.
    fn process_task(&self, task: Task) {
        let n = self.mem.get(task.idx);
        let mut guard = ProcessingGuard::new(&n.status, MetricKind::ProcessTask);
        let data: &mut ProcessingData = n.cache.get_ref();

        // Bias: hold +1 on waiting_cnt so a notifier cannot reach zero and
        // re-enqueue us while we are mid-scan.
        n.waiting_cnt.fetch_add(1, Ordering::Relaxed);

        if let Some(result) = self.update_node(&task, n, data) {
            // Publish order (critical for pushers seeing CLOSED):
            //   1. Write result into cache (plain store).
            //   2. AcqRel-swap dependents_head to CLOSED — captures chain.
            //   3. Release-store FINISHED on status.
            // Any pusher that observes CLOSED via Acquire on the head (or
            // FINISHED via Acquire on status) is guaranteed to see the
            // result value.
            n.cache.set_value(result);
            let drained = n.dependents_head.close();
            guard.finish(); // PROCESSING -> FINISHED (Release)
            // SAFETY: After FINISHED + CLOSED, no other thread may access
            // `ProcessingData` via `cache.ptr` (it's been overwritten by
            // `set_value` anyway) or via the dependents path. The local
            // `data` pointer into the Box is the sole live reference.
            unsafe { drop(Box::from_raw(data as *mut ProcessingData)) };
            self.drain_and_notify(drained, task.size_log2 + 1);
        } else {
            // Release PROCESSING first so any re-enqueue can immediately
            // re-acquire it without spinning on our guard.
            drop(guard);
            let prev = n.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
            if prev == 1 {
                // All pending dependencies finished during our scan; nothing
                // else will re-enqueue us, so do it ourselves.
                self.queue.push(task);
            }
        }
    }

    /// Compute node result by processing its children/dependencies.
    ///
    /// Returns `Some(result)` if computation completes, `None` if waiting for dependencies.
    ///
    /// ## Hashlife Algorithm
    ///
    /// For non-leaf nodes, computation happens in stages:
    /// 1. **Stage 1** (if `both_stages`): Compute 9 overlapping children
    /// 2. **Stage 2**: Compute 4 final children from the 9 (or directly if single-stage)
    /// 3. Combine the 4 children into final result
    ///
    /// ## Dependency handling
    ///
    /// When a child is not ready, [`handle_dependency_and_track`] is called
    /// with `parent = n`. It atomically updates `n.waiting_cnt` as follows:
    /// - `Ready`: no change (dependency already done).
    /// - `StartedByThisThread` / `StartedByOtherThread`: `n.waiting_cnt`
    ///   was incremented; we have registered as a dependent of the child.
    fn update_node(
        &self,
        task: &Task,
        n: &QuadTreeNode<Meta>,
        data: &mut ProcessingData,
    ) -> Option<Idx> {
        let both_stages = self.generations_log2 + 2 >= task.size_log2;
        let [nw, ne, sw, se] = n.parts();
        if task.size_log2 == LEAF_SIZE_LOG2 + 1 {
            // base case: node consists of leaves
            let steps = if both_stages {
                LEAF_SIZE / 2
            } else {
                1 << self.generations_log2
            };
            return Some(algorithm::update_leaves(&self.mem, nw, ne, sw, se, steps));
        }

        if data.mask4_waiting == 0 {
            // arr4 is not ready
            if !both_stages {
                data.arr = algorithm::nine_children_disjoint(
                    &self.mem,
                    nw,
                    ne,
                    sw,
                    se,
                    task.size_log2 - 1,
                );
            } else {
                if data.mask9_waiting == 0 {
                    data.arr = algorithm::nine_children_overlapping(&self.mem, nw, ne, sw, se);
                    data.mask9_waiting = 0b1_1111_1111;
                }

                for (i, x) in data.arr.iter_mut().enumerate() {
                    if data.mask9_waiting & (1 << i) == 0 {
                        continue;
                    }
                    let d = self.mem.get(*x);
                    match handle_dependency_and_track(n, d, task.idx) {
                        DependencyHandlingResult::Ready => {
                            data.mask9_waiting &= !(1 << i);
                            *x = d.cache.get_value();
                        }
                        DependencyHandlingResult::StartedByThisThread => {
                            self.queue.push(Task::new(*x, task.size_log2 - 1));
                        }
                        DependencyHandlingResult::StartedByOtherThread => {}
                    }
                }

                if data.mask9_waiting != 0 {
                    return None;
                }
            }

            let arr4 = algorithm::four_children_overlapping(&self.mem, &data.arr);
            data.arr[..4].copy_from_slice(&arr4);
            data.mask4_waiting = 0b1111;
        }

        for (i, x) in data.arr.iter_mut().take(4).enumerate() {
            if data.mask4_waiting & (1 << i) == 0 {
                continue;
            }
            let d = self.mem.get(*x);
            match handle_dependency_and_track(n, d, task.idx) {
                DependencyHandlingResult::Ready => {
                    data.mask4_waiting &= !(1 << i);
                    *x = d.cache.get_value();
                }
                DependencyHandlingResult::StartedByThisThread => {
                    self.queue.push(Task::new(*x, task.size_log2 - 1));
                }
                DependencyHandlingResult::StartedByOtherThread => {}
            }
        }

        if data.mask4_waiting != 0 {
            return None;
        }

        Some(
            self.mem
                .find_or_create_node(data.arr[0], data.arr[1], data.arr[2], data.arr[3]),
        )
    }

    /// Walk the drained dependents chain produced by `DepHead::close` and
    /// notify each dependent that this node has finished.
    ///
    /// Each dependent receives `fetch_sub(1)` on its `waiting_cnt`; the
    /// notifier whose decrement brings the counter to zero re-enqueues it.
    fn drain_and_notify(&self, drained: DepState, dep_size_log2: u32) {
        dep_stack::drain(drained, |dep_idx| {
            let dep = self.mem.get(dep_idx);
            let prev = dep.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
            // `prev == 1` means `waiting_cnt` just reached 0, and no other
            // thread will see it hit zero: we are the exclusive re-enqueuer.
            if prev == 1 {
                self.queue.push(Task::new(dep_idx, dep_size_log2));
            }
            record_metric(0, MetricKind::NotifyDep);
        });
    }
}

/// Check if a status field indicates FINISHED.
pub(super) fn is_finished(status: &AtomicU8) -> bool {
    status.load(Ordering::Acquire) == status::FINISHED
}

/// Initialize a node for processing by transitioning NOT_STARTED → PROCESSING → PENDING.
///
/// Returns `true` if this thread successfully claimed the node, `false` if
/// another thread did.
///
/// Steps:
/// 1. CAS(NOT_STARTED → PROCESSING) to claim the node.
/// 2. Allocate and store `ProcessingData` pointer in `cache`.
/// 3. If `initial_parent` is provided, register it as the first dependent.
/// 4. Release-store PENDING (publishes the fresh `ProcessingData` pointer
///    and the initial dependent to observers).
pub(super) fn start_processing_node<Meta: Default + Sync>(
    node: &QuadTreeNode<Meta>,
    initial_parent: Option<Idx>,
) -> bool {
    if node
        .status
        .compare_exchange(
            status::NOT_STARTED,
            status::PROCESSING,
            Ordering::Relaxed,
            Ordering::Relaxed,
        )
        .is_err()
    {
        record_status_claim_fail();
        return false;
    }

    let pd = Box::into_raw(Box::new(ProcessingData::default()));
    node.cache.set_ptr(pd);
    if let Some(parent_idx) = initial_parent {
        // The stack cannot be CLOSED here: only the owner closes, and the
        // owner (this thread) has just claimed the node. No one else can
        // have run `close` yet.
        let res = node.dependents_head.push(parent_idx);
        debug_assert!(matches!(res, PushResult::Pushed));
    }
    node.status.store(status::PENDING, Ordering::Release);
    record_status_claim_success();
    true
}

/// RAII guard for PROCESSING status on a single node.
///
/// Acquires PROCESSING status on creation (spin-waits on PENDING), releases
/// it on drop. This is the owner-exclusive lock for the owner-private
/// `ProcessingData` box.
///
/// - If [`finish`] is called: status transitions to FINISHED and `drop`
///   becomes a no-op.
/// - Otherwise `drop` transitions the status back to PENDING.
pub(super) struct ProcessingGuard<'a> {
    status: &'a AtomicU8,
    released: bool,
}

impl<'a> ProcessingGuard<'a> {
    /// Acquire PROCESSING status, spinning until PENDING.
    pub(super) fn new(status: &'a AtomicU8, kind: MetricKind) -> Self {
        let mut spin_count = 0u64;
        loop {
            if status
                .compare_exchange_weak(
                    status::PENDING,
                    status::PROCESSING,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                )
                .is_ok()
            {
                record_metric(spin_count, kind);
                return Self {
                    status,
                    released: false,
                };
            }
            while status.load(Ordering::Relaxed) != status::PENDING {
                spin_count += 1;
                hint::spin_loop();
            }
        }
    }

    /// Mark node as FINISHED and prevent `drop` from reverting to PENDING.
    pub(super) fn finish(&mut self) {
        self.status.store(status::FINISHED, Ordering::Release);
        self.released = true;
    }
}

impl<'a> Drop for ProcessingGuard<'a> {
    fn drop(&mut self) {
        if !self.released {
            self.status.store(status::PENDING, Ordering::Release);
        }
    }
}

/// Result of attempting to handle a dependency.
enum DependencyHandlingResult {
    /// Dependency already computed, result available in cache.
    Ready,
    /// This thread successfully claimed the dependency for processing.
    StartedByThisThread,
    /// Another thread is processing the dependency; we registered as a
    /// dependent.
    StartedByOtherThread,
}

/// Handle a dependency and update the parent's `waiting_cnt` accordingly.
///
/// Fast path: if the child is already FINISHED, no counter write happens.
///
/// Slow path: we pre-increment `parent.waiting_cnt` and then register as a
/// dependent of the child via the lock-free stack. The pre-increment ordering
/// matters: if the child's owner finishes and drains while we are pushing,
/// our successful push happens-before its AcqRel swap (Release on our CAS,
/// Acquire on its swap), so its eventual `fetch_sub` on
/// `parent.waiting_cnt` sees our increment. Conversely, if the push observes
/// CLOSED, we undo the pre-increment.
fn handle_dependency_and_track<Meta: Default + Sync>(
    parent: &QuadTreeNode<Meta>,
    child: &QuadTreeNode<Meta>,
    parent_idx: Idx,
) -> DependencyHandlingResult {
    // Fast path: child already done. No counter mutation.
    if is_finished(&child.status) {
        return DependencyHandlingResult::Ready;
    }

    // Pre-increment so a child that finishes during our push still sees a
    // consistent counter when it eventually `fetch_sub`s.
    parent.waiting_cnt.fetch_add(1, Ordering::Relaxed);

    let result = register_as_dependent(child, parent_idx);
    if matches!(result, DependencyHandlingResult::Ready) {
        // The child finished before we could register: undo the pre-increment.
        // `Relaxed` is sufficient because we've done no publishing that a
        // notifier of ours would rely on — we never added a dependent here.
        parent.waiting_cnt.fetch_sub(1, Ordering::Relaxed);
    }
    result
}

/// Register `parent_idx` as a dependent of `child`.
///
/// - If `child.status == FINISHED`, returns `Ready`.
/// - If `child.status == NOT_STARTED` and we successfully CAS to
///   PROCESSING, fully initialize the child's `ProcessingData` and register
///   `parent_idx` as its first dependent; return `StartedByThisThread`.
/// - Otherwise, push onto the child's lock-free dependents stack. A
///   successful push returns `StartedByOtherThread`; observing `CLOSED`
///   (the child has just finished) returns `Ready`.
fn register_as_dependent<Meta: Default + Sync>(
    child: &QuadTreeNode<Meta>,
    parent_idx: Idx,
) -> DependencyHandlingResult {
    loop {
        let status = child.status.load(Ordering::Acquire);
        match status {
            status::FINISHED => return DependencyHandlingResult::Ready,
            status::NOT_STARTED => {
                if start_processing_node(child, Some(parent_idx)) {
                    return DependencyHandlingResult::StartedByThisThread;
                }
                // CAS lost to another thread; re-read status and retry.
            }
            status::PROCESSING | status::PENDING => {
                match child.dependents_head.push(parent_idx) {
                    PushResult::Pushed => {
                        record_metric(0, MetricKind::HandleDep);
                        return DependencyHandlingResult::StartedByOtherThread;
                    }
                    PushResult::Closed => return DependencyHandlingResult::Ready,
                }
            }
            other => panic!("unexpected status {other}"),
        }
    }
}
