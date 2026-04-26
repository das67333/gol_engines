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
//! Each node carries an `AtomicU8` interpreted as a bit-set (see [`status`]).
//! The bits divide responsibilities so that independent transitions never
//! contend on a single critical section:
//!
//! ```text
//!     NOT_STARTED ─CAS─► PROCESSING ─store─► PENDING ◄──fetch_xor── ACTIVE
//!                        (init barrier:        ▲                      │
//!                         pd not yet           │  CAS preserving      │
//!                         installed)           │  DEPS_LOCK           │
//!                                              └──────────────────────┘
//!                                                      │
//!                                                      │ CAS (DEPS_LOCK==0)
//!                                                      ▼
//!                                                  PROCESSING ─store─► FINISHED
//!                                                  (finish barrier:
//!                                                   pd is being drained,
//!                                                   value is being written)
//! ```
//!
//! Key transitions:
//! - `NOT_STARTED → PROCESSING`: A thread claims the node and is about to
//!   install its [`ProcessingData`].
//! - `PROCESSING → PENDING`: Init barrier ends; pushers may now register
//!   dependents under `DEPS_LOCK`.
//! - `PENDING → ACTIVE`: A worker dequeues the task and starts computing
//!   (preserving any currently-held `DEPS_LOCK`).
//! - `ACTIVE → PENDING`: Worker is parking the node while waiting for
//!   dependencies (preserves `DEPS_LOCK`).
//! - `ACTIVE → PROCESSING`: Finish barrier; spins until `DEPS_LOCK` is
//!   clear, then no pusher can observe `pd` again.
//! - `PROCESSING → FINISHED`: Result published, dependents drained.
//!
//! ## Dependents-list synchronization
//!
//! [`ProcessingData::dependents`] is mutated by two parties:
//! - The owner during [`start_processing_node`] (exclusive: status is
//!   `PROCESSING`, pushers spin) and during the finish barrier (exclusive:
//!   status is `PROCESSING`, no `DEPS_LOCK` is held).
//! - Pushers in [`handle_dependency`] under the transient `DEPS_LOCK` bit,
//!   which can coexist with `PENDING` or `ACTIVE` so that the owner is never
//!   blocked from running its computation.
//!
//! ## `waiting_cnt` synchronization
//!
//! [`ProcessingData::waiting_cnt`] is an [`AtomicU16`] manipulated lock-free
//! with a bias trick: the owner adds [`WAITING_BIAS`] before scanning its
//! children, increments by one for every dependency it registers, and
//! subtracts the bias after the scan. Notifiers do `fetch_sub(1)`. The bias
//! prevents a notifier from reaching zero while the owner is mid-scan; the
//! thread that observes the counter become zero (either the owner upon
//! `fetch_sub(BIAS)` or the last notifier) re-queues the parent task.

use super::{
    LEAF_SIZE, LEAF_SIZE_LOG2, algorithm,
    hashlife::HashLifeEngine,
    hashtable::{Idx, NodeStore, NodeStoreRef},
    node::QuadTreeNode,
    sharded_statistics::*,
    status,
};
use crossbeam::deque::{Steal, Stealer, Worker};
use smallvec::{SmallVec, smallvec};
use std::{
    hint, mem,
    sync::atomic::{AtomicU8, AtomicU16, Ordering},
    thread,
    time::Duration,
};

/// Bias added to `waiting_cnt` while the owner is scanning children. Any
/// value strictly greater than the maximum number of in-flight registrations
/// per scan suffices; we choose a clearly out-of-band value so the counter
/// never collides with a real outstanding-dependency count.
const WAITING_BIAS: u16 = 1 << 15;

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
    /// Count of dependencies still being computed. The node resumes when this
    /// reaches 0. Manipulated lock-free with the bias trick (see module docs).
    waiting_cnt: AtomicU16,
    /// Nodes that registered as dependents of this node.
    /// Notified when this node finishes.
    ///
    /// Mutated by the owner exclusively during the init/finish barriers, and
    /// by pushers in parallel under [`status::DEPS_LOCK`].
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
        let timer = std::time::Instant::now();
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
                total_stats.merge_from(&handle.join().unwrap());
            }
        });

        if self.mem.exceeds_load_factor() {
            self.free_orphaned_processing_data();
            return None;
        }

        assert!(is_finished(&self.mem.get(self.root).status));
        println!("Time spent on hashlife executor: {:?}", timer.elapsed());
        println!("Nodes count: {}", self.mem.len());
        #[cfg(feature = "statistics")]
        println!("{total_stats}");

        Some(root_node.cache.get_value())
    }

    /// Drop `ProcessingData` boxes orphaned by cancellation. Must be called
    /// from a single-threaded context after `thread::scope` has joined; only
    /// PENDING slots own a live box at that point.
    fn free_orphaned_processing_data(&self) {
        for idx in 0..self.mem.capacity() {
            let n = self.mem.get(idx as Idx);
            let status = n.status.load(Ordering::Relaxed);
            if status == status::PENDING {
                let pd: &mut ProcessingData = n.cache.get_ref();
                // SAFETY: produced by `Box::into_raw` in
                // `start_processing_node`; all workers have joined.
                unsafe { drop(Box::from_raw(pd as *mut ProcessingData)) };
            }
        }
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

    /// Process a single task: compute the node's result or park it.
    ///
    /// Flow:
    /// 1. Acquire owner-mutex by transitioning `PENDING → ACTIVE` (preserving
    ///    any currently-held `DEPS_LOCK`).
    /// 2. Call `update_node` to compute the result or register dependencies.
    /// 3. If a result is ready: cross the finish barrier (`ACTIVE → PROCESSING`
    ///    once `DEPS_LOCK` clears), drain the dependents list, publish the
    ///    value, transition to `FINISHED`, and notify dependents.
    /// 4. If dependencies are needed: guard drop transitions `ACTIVE → PENDING`
    ///    while preserving `DEPS_LOCK`.
    fn process_task(&self, task: Task) {
        let n = self.mem.get(task.idx);
        let mut guard = ProcessingGuard::new(&n.status, MetricKind::ProcessTask);
        let data: &mut ProcessingData = n.cache.get_ref();
        if let Some(result) = self.update_node(&task, n.parts(), data) {
            // Cross the finish barrier so pushers stop touching `data` and the
            // cache slot, then drain dependents, publish the value, and mark
            // the node FINISHED.
            guard.enter_finish_barrier(MetricKind::NotifyDep);
            let mut dependents = SmallVec::new();
            mem::swap(&mut data.dependents, &mut dependents);
            n.cache.set_value(result);
            guard.publish_finished();
            unsafe { drop(Box::from_raw(data as *mut ProcessingData)) };
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
    /// - `Ready`: Child already computed, use cached result
    /// - `StartedByThisThread`: We claimed the child, register as dependent, push to local queue
    /// - `StartedByOtherThread`: Another thread processing it, register as dependent
    ///
    /// When the function returns `None` because at least one child is still
    /// in flight, ownership of "wake-up duty" is transferred via the
    /// `waiting_cnt` bias trick: whichever thread observes the counter become
    /// zero (this owner via `fetch_sub(WAITING_BIAS)` or the last notifier
    /// via `fetch_sub(1)`) is responsible for re-queuing the parent task.
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

                // Bias `waiting_cnt` so concurrent notifiers cannot drive it
                // to zero while we are still scanning.
                data.waiting_cnt
                    .fetch_add(WAITING_BIAS, Ordering::Relaxed);
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
                            data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                            self.queue.push(Task::new(*x, task.size_log2 - 1));
                        }
                        DependencyHandlingResult::StartedByOtherThread => {
                            data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                }
                let prev = data.waiting_cnt.fetch_sub(WAITING_BIAS, Ordering::AcqRel);

                if data.mask9_waiting != 0 {
                    if prev == WAITING_BIAS {
                        // Every dependency we registered already notified
                        // before our `fetch_sub`; re-queue ourselves so the
                        // mask gets re-scanned with their now-`Ready` status.
                        self.queue.push(Task::new(task.idx, task.size_log2));
                    }
                    return None;
                }
            }

            let arr4 = algorithm::four_children_overlapping(&self.mem, &data.arr);
            data.arr[..4].copy_from_slice(&arr4);
            data.mask4_waiting = 0b1111;
        }

        data.waiting_cnt
            .fetch_add(WAITING_BIAS, Ordering::Relaxed);
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
                    data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    self.queue.push(Task::new(*x, task.size_log2 - 1));
                }
                DependencyHandlingResult::StartedByOtherThread => {
                    data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                }
            }
        }
        let prev = data.waiting_cnt.fetch_sub(WAITING_BIAS, Ordering::AcqRel);

        if data.mask4_waiting != 0 {
            if prev == WAITING_BIAS {
                self.queue.push(Task::new(task.idx, task.size_log2));
            }
            return None;
        }

        Some(
            self.mem
                .find_or_create_node(data.arr[0], data.arr[1], data.arr[2], data.arr[3]),
        )
    }

    /// Notify dependent nodes that this dependency has completed.
    ///
    /// For each dependent we atomically decrement its `waiting_cnt`. The
    /// thread that drives the counter to zero (this notifier or the owner's
    /// own `fetch_sub(WAITING_BIAS)` at the end of its scan) is responsible
    /// for re-queuing the parent. Notifiers do not take any lock on the
    /// dependent node: `waiting_cnt` is atomic, and `ProcessingData` stays
    /// alive until `FINISHED` (which only the owner can publish, after the
    /// counter has dropped to zero).
    fn notify_dependents(&self, task: &Task, dependents: Dependents) {
        for &dependent in dependents.iter() {
            let n = self.mem.get(dependent);
            let dep_data: &ProcessingData = n.cache.get_ref();
            let prev = dep_data.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
            if prev == 1 {
                self.queue.push(Task::new(dependent, task.size_log2 + 1));
            }
        }
    }
}

/// Check if a status field indicates FINISHED.
pub(super) fn is_finished(status: &AtomicU8) -> bool {
    status.load(Ordering::Acquire) & status::FINISHED != 0
}

/// Initialize a node for processing by transitioning `NOT_STARTED → PROCESSING → PENDING`.
///
/// Returns `true` if this thread successfully claimed the node, `false` if another thread did.
///
/// Steps:
/// 1. CAS `NOT_STARTED → PROCESSING` claims the node and erects an init
///    barrier (pushers spin while `PROCESSING` is observed).
/// 2. Allocate and install [`ProcessingData`].
/// 3. `fetch_xor` flips `PROCESSING → PENDING`, releasing the barrier with
///    Release semantics so subsequent pushers observe the freshly-installed
///    `ProcessingData`.
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
        record_status_claim_fail();
        return false;
    }

    let pd = ProcessingData {
        dependents,
        ..Default::default()
    };
    node.cache.set_ptr(Box::into_raw(Box::new(pd)));
    // Atomically swap the `PROCESSING` bit for `PENDING` while preserving any
    // other bits (none should be set during init, but `fetch_xor` makes the
    // intent explicit).
    node.status
        .fetch_xor(status::PROCESSING | status::PENDING, Ordering::Release);
    record_status_claim_success();
    true
}

/// RAII guard for the owner-mutex bit (`ACTIVE`).
///
/// `new` transitions `PENDING → ACTIVE` while preserving any currently-held
/// `DEPS_LOCK` overlay bit. If neither `enter_finish_barrier` nor
/// `publish_finished` is called, `Drop` reverts `ACTIVE → PENDING` (again
/// preserving `DEPS_LOCK`).
pub(super) struct ProcessingGuard<'a> {
    status: &'a AtomicU8,
    released: bool,
}

impl<'a> ProcessingGuard<'a> {
    /// Acquire the owner-mutex by transitioning `PENDING → ACTIVE`. Spins
    /// while `PENDING` is not observable (e.g. `PROCESSING` init barrier).
    pub(super) fn new(status: &'a AtomicU8, kind: MetricKind) -> Self {
        let mut spin_count = 0u64;
        loop {
            let cur = status.load(Ordering::Acquire);
            if cur & status::PENDING != 0 {
                let want = (cur & !status::PENDING) | status::ACTIVE;
                if status
                    .compare_exchange_weak(cur, want, Ordering::AcqRel, Ordering::Relaxed)
                    .is_ok()
                {
                    record_metric(spin_count, kind);
                    return Self {
                        status,
                        released: false,
                    };
                }
            }
            spin_count += 1;
            hint::spin_loop();
        }
    }

    /// Cross the finish barrier: `ACTIVE → PROCESSING`, spinning until
    /// `DEPS_LOCK` is clear. After this returns, no pusher can observe the
    /// node as live, so the caller may safely write the result into the
    /// cache slot and drain the dependents list.
    pub(super) fn enter_finish_barrier(&mut self, kind: MetricKind) {
        let mut spin_count = 0u64;
        while self
            .status
            .compare_exchange_weak(
                status::ACTIVE,
                status::PROCESSING,
                Ordering::AcqRel,
                Ordering::Relaxed,
            )
            .is_err()
        {
            spin_count += 1;
            hint::spin_loop();
        }
        record_metric(spin_count, kind);
        // From now on `Drop` must not revert: we have left `ACTIVE` for good.
        self.released = true;
    }

    /// Publish the terminal state: `PROCESSING → FINISHED`. Must be called
    /// after [`Self::enter_finish_barrier`] and after the result has been
    /// written into the cache slot.
    pub(super) fn publish_finished(self) {
        self.status.store(status::FINISHED, Ordering::Release);
        mem::forget(self);
    }
}

impl<'a> Drop for ProcessingGuard<'a> {
    fn drop(&mut self) {
        if !self.released {
            // `ACTIVE → PENDING` while preserving `DEPS_LOCK`.
            self.status
                .fetch_xor(status::ACTIVE | status::PENDING, Ordering::Release);
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
///
/// Registration uses the [`status::DEPS_LOCK`] overlay bit, which can coexist
/// with both `PENDING` and `ACTIVE`. This means a pusher never has to wait
/// for the owner's compute burst — only for the brief init / finish
/// barriers (encoded as `PROCESSING`) or for another concurrent pusher.
fn handle_dependency<Meta: Default + Sync>(
    n: &QuadTreeNode<Meta>,
    task: &Task,
) -> DependencyHandlingResult {
    let mut spin_count = 0u64;
    loop {
        let cur = n.status.load(Ordering::Acquire);
        if cur & status::FINISHED != 0 {
            record_metric(spin_count, MetricKind::HandleDep);
            return DependencyHandlingResult::Ready;
        }
        if cur == status::NOT_STARTED {
            if start_processing_node(n, smallvec![task.idx]) {
                record_metric(spin_count, MetricKind::HandleDep);
                return DependencyHandlingResult::StartedByThisThread;
            }
            // Lost the race; observe the new state on the next iteration.
            continue;
        }
        if cur & status::PROCESSING != 0 {
            // Init or finish barrier; brief by construction.
            spin_count += 1;
            hint::spin_loop();
            continue;
        }
        if cur & status::DEPS_LOCK != 0 {
            // Another pusher is mutating the dependents list.
            spin_count += 1;
            hint::spin_loop();
            continue;
        }
        // `cur` has `PENDING` or `ACTIVE` set and no `DEPS_LOCK`. Try to
        // grab the lock without disturbing the work-status bits.
        let want = cur | status::DEPS_LOCK;
        if n
            .status
            .compare_exchange_weak(cur, want, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
        {
            n.cache
                .get_ref::<ProcessingData>()
                .dependents
                .push(task.idx);
            n.status
                .fetch_and(!status::DEPS_LOCK, Ordering::Release);
            record_metric(spin_count, MetricKind::HandleDep);
            return DependencyHandlingResult::StartedByOtherThread;
        }
    }
}
