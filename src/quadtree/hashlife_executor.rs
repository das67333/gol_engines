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
//!                │ when waiting  │ when all dependencies ready
//!                │ for deps      │
//!                ▼               │
//!     ┌──────────────────────┐   │
//!     │     PENDING (2)      │ ──┘
//!     └──────────────────────┘
//! ```
//!
//! Key transitions:
//! - `NOT_STARTED → PROCESSING`: Thread claims node for processing
//! - `PROCESSING → PENDING`: Node needs to wait for dependencies
//! - `PENDING → PROCESSING`: All dependencies ready, resume processing
//! - `PROCESSING → FINISHED`: Computation complete, result cached

use super::{
    LEAF_SIZE, LEAF_SIZE_LOG2, algorithm,
    hashlife::HashLifeEngine,
    hashtable::{Idx, NodeStore, NodeStoreRef},
    node::QuadTreeNode,
    sharded_statistics::ExecutionStatistics,
    status,
};
use crossbeam::deque::{Steal, Stealer, Worker};
use smallvec::{SmallVec, smallvec};
use std::{
    hint, mem,
    sync::atomic::{AtomicU8, Ordering},
    thread,
    time::Duration,
};

/// List of nodes waiting for this node's result.
///
/// Optimized with `SmallVec<[_; 2]>` to avoid heap allocation in the common case,
/// since almost every node (>>99.99%) has 1 dependent. A capacity of 2 is used
/// because it does not increase the struct size compared to a capacity of 1.
type Dependents = SmallVec<[Idx; 2]>;

/// Temporary data allocated during node processing.
///
/// Heap-allocated when processing starts, freed when node reaches FINISHED state.
/// Stored via pointer in the node's `cache` field.
#[derive(Default)]
struct ProcessingData {
    /// Intermediate child node results (up to 9 for overlapping, 4 for final stage).
    arr: [Idx; 9],
    /// Bitmask: bit `i` set if `arr[i]` (among first 9) is not yet computed.
    mask9_waiting: u32,
    /// Bitmask: bit `i` set if `arr[i]` (among first 4) is not yet computed.
    mask4_waiting: u32,
    /// Count of dependencies still being computed. Node can resume when this reaches 0.
    waiting_cnt: u32,
    /// Nodes that registered as dependents of this node.
    /// Notified when this node finishes.
    dependents: Dependents,
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
    pub(super) fn fetch_task(&mut self, stats: &mut ExecutionStatistics) -> Option<T> {
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
        let result = self.try_steal(self.last_victim, stats);
        stats.on_steal_from_last_victim(&result);
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
                && let Some(task) = self.try_steal(victim_id, stats)
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

    fn try_steal(&mut self, victim_id: usize, stats: &mut ExecutionStatistics) -> Option<T> {
        loop {
            let result = self.stealers[victim_id]
                .steal_batch_with_limit_and_pop(self.queue, Self::STEAL_BATCH_SIZE);
            stats.on_steal_attempt(&result);
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
        start_processing_node(root_node, smallvec![]);
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
                total_stats.merge(&handle.join().unwrap());
            }
        });

        if self.mem.exceeds_load_factor() {
            return None;
        }

        assert!(is_finished(&self.mem.get(self.root).status));
        println!("Nodes count: {}", self.mem.len());
        total_stats.print();

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
        let mut stats = ExecutionStatistics::new();

        while let Some(task) = fetcher.fetch_task(&mut stats) {
            self.process_task(task);
        }
        stats
    }

    /// Process a single task: compute the node's result or wait for dependencies.
    ///
    /// Flow:
    /// 1. Acquire PROCESSING status via `ProcessingGuard`
    /// 2. Call `update_node` to compute result or identify dependencies
    /// 3. If result ready: cache it, notify dependents, mark FINISHED
    /// 4. If dependencies needed: guard drops, status returns to PENDING
    fn process_task(&self, task: Task) {
        let n = self.mem.get(task.idx);
        let mut guard = ProcessingGuard::new(&n.status);
        let data: &mut ProcessingData = n.cache.get_ref();
        if let Some(result) = self.update_node(&task, n.parts(), data) {
            n.cache.set_value(result);
            let mut dependents = SmallVec::new();
            mem::swap(&mut data.dependents, &mut dependents);
            guard.finish(); // Mark as FINISHED
            unsafe { drop(Box::from_raw(data as *mut ProcessingData)) } // Free ProcessingData
            self.notify_dependents(&task, dependents);
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
    /// ## Dependency Handling
    ///
    /// When a child is not ready:
    /// - `DependencyIsReady`: Child already computed, use cached result
    /// - `StartedByThisThread`: We claimed the child, register as dependent, push to local queue
    /// - `StartedByOtherThread`: Another thread processing it, register as dependent
    fn update_node(&self, task: &Task, parts: [Idx; 4], data: &mut ProcessingData) -> Option<Idx> {
        let both_stages = self.generations_log2 + 2 >= task.size_log2;
        let [nw, ne, sw, se] = parts;
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

                let mut waiting_cnt = 0;
                for (i, x) in data.arr.iter_mut().enumerate() {
                    if data.mask9_waiting & (1 << i) == 0 {
                        continue;
                    }
                    let d = self.mem.get(*x);
                    match handle_dependency(d, task) {
                        DependencyHandlingResult::Ready => {
                            data.mask9_waiting &= !(1 << i);
                            *x = d.cache.get_value();
                        }
                        DependencyHandlingResult::StartedByThisThread => {
                            self.queue.push(Task::new(*x, task.size_log2 - 1));
                            waiting_cnt += 1;
                        }
                        DependencyHandlingResult::StartedByOtherThread => {
                            waiting_cnt += 1;
                        }
                    }
                }

                if data.mask9_waiting != 0 {
                    data.waiting_cnt = waiting_cnt;
                    return None;
                }
            }

            let arr4 = algorithm::four_children_overlapping(&self.mem, &data.arr);
            data.arr[..4].copy_from_slice(&arr4);
            data.mask4_waiting = 0b1111;
        }

        let mut waiting_cnt = 0;
        for (i, x) in data.arr.iter_mut().take(4).enumerate() {
            if data.mask4_waiting & (1 << i) == 0 {
                continue;
            }
            let d = self.mem.get(*x);
            match handle_dependency(d, task) {
                DependencyHandlingResult::Ready => {
                    data.mask4_waiting &= !(1 << i);
                    *x = d.cache.get_value();
                }
                DependencyHandlingResult::StartedByThisThread => {
                    self.queue.push(Task::new(*x, task.size_log2 - 1));
                    waiting_cnt += 1;
                }
                DependencyHandlingResult::StartedByOtherThread => {
                    waiting_cnt += 1;
                }
            }
        }

        if data.mask4_waiting != 0 {
            data.waiting_cnt = waiting_cnt;
            return None;
        }

        Some(
            self.mem
                .find_or_create_node(data.arr[0], data.arr[1], data.arr[2], data.arr[3]),
        )
    }

    /// Notify dependent nodes that this dependency has completed.
    ///
    /// For each dependent:
    /// 1. Acquire PROCESSING status
    /// 2. Decrement its `waiting_cnt`
    /// 3. If `waiting_cnt` reaches 0, re-queue for processing
    fn notify_dependents(&self, task: &Task, dependents: Dependents) {
        for &dependent in dependents.iter() {
            let n = self.mem.get(dependent);
            let waiting_cnt = {
                let _guard = ProcessingGuard::new(&n.status);
                let dep_data: &mut ProcessingData = n.cache.get_ref();
                dep_data.waiting_cnt -= 1;
                dep_data.waiting_cnt
            };
            if waiting_cnt == 0 {
                self.queue.push(Task::new(dependent, task.size_log2 + 1));
            }
        }
    }
}

/// Check if a status field indicates FINISHED.
pub(super) fn is_finished(status: &AtomicU8) -> bool {
    status.load(Ordering::Acquire) == status::FINISHED
}

/// Initialize a node for processing by transitioning NOT_STARTED → PROCESSING → PENDING.
///
/// Returns `true` if this thread successfully claimed the node, `false` if another thread did.
///
/// Steps:
/// 1. CAS(NOT_STARTED → PROCESSING) to claim the node
/// 2. Allocate and store ProcessingData
/// 3. Store PENDING status (node ready to be processed)
fn start_processing_node<Meta: Default + Sync>(
    node: &QuadTreeNode<Meta>,
    dependents: Dependents,
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
        return false;
    }

    let pd = ProcessingData {
        dependents,
        ..Default::default()
    };
    node.cache.set_ptr(Box::into_raw(Box::new(pd)));
    node.status.store(status::PENDING, Ordering::Release);
    true
}

/// Atomically transition status from `from` to `to`, spinning until successful.
fn atomic_transition_loop(a: &AtomicU8, from: u8, to: u8) {
    while a
        .compare_exchange_weak(from, to, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        while a.load(Ordering::Relaxed) != from {
            hint::spin_loop();
        }
    }
}

/// RAII guard for PROCESSING status.
///
/// Acquires PROCESSING status on creation, releases it on drop.
/// - If `finish()` called: transitions to FINISHED
/// - If dropped without `finish()`: transitions back to PENDING
pub(super) struct ProcessingGuard<'a> {
    status: &'a AtomicU8,
    released: bool,
}

impl<'a> ProcessingGuard<'a> {
    /// Acquire PROCESSING status, spinning until PENDING.
    pub(super) fn new(status: &'a AtomicU8) -> Self {
        atomic_transition_loop(status, status::PENDING, status::PROCESSING);
        Self {
            status,
            released: false,
        }
    }
}

impl<'a> ProcessingGuard<'a> {
    /// Mark node as FINISHED and prevent drop from reverting to PENDING.
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
    /// Dependency already computed, result available in cache
    Ready,
    /// This thread successfully claimed the dependency for processing
    StartedByThisThread,
    /// Another thread is processing the dependency, we registered as dependent
    StartedByOtherThread,
}

/// Handle a dependency: check if ready, start processing, or register as dependent.
fn handle_dependency<Meta: Default + Sync>(
    n: &QuadTreeNode<Meta>,
    task: &Task,
) -> DependencyHandlingResult {
    let status = n.status.load(Ordering::Acquire);
    if status == status::FINISHED {
        return DependencyHandlingResult::Ready;
    }

    if status == status::NOT_STARTED && start_processing_node(n, smallvec![task.idx]) {
        return DependencyHandlingResult::StartedByThisThread;
    }

    loop {
        match n.status.compare_exchange_weak(
            status::PENDING,
            status::PROCESSING,
            Ordering::Acquire,
            Ordering::Acquire,
        ) {
            Ok(_) => {
                n.cache
                    .get_ref::<ProcessingData>()
                    .dependents
                    .push(task.idx);
                n.status.store(status::PENDING, Ordering::Release);
                return DependencyHandlingResult::StartedByOtherThread;
            }
            Err(status::FINISHED) => return DependencyHandlingResult::Ready,
            Err(status::PROCESSING) => {
                while n.status.load(Ordering::Relaxed) == status::PROCESSING {
                    hint::spin_loop()
                }
            }
            Err(value) => panic!("Unexpected status in handle_dependency: {}", value),
        }
    }
}
