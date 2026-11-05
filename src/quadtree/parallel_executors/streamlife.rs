//! # Parallel `StreamLife` Executor
//!
//! Work-stealing parallel executor for the `StreamLife` algorithm's
//! `update_binode` operation, with cross-engine async cooperation: `HashLife`
//! sub-results required by `update_binode`'s solitonic / base fast-paths are
//! computed asynchronously rather than via a synchronous recursive call.
//!
//! ## Two queues per worker
//!
//! Each worker holds two task deques:
//! - `bi_queue: TaskQueue<BiTask>` — binode tasks (the existing work item).
//! - `hash_queue: TaskQueue<Task>` — `HashLife` tasks descended from binode
//!   Phases Solitonic / Base.
//!
//! Pop policy: local LIFO hash first to finish dependencies, then local bi.
//! Stealing prefers bi, then hash, with a complete scan before idle workers park.
//! `HashLife`'s pure-engine path is unchanged: it still uses a single
//! crossbeam `Worker<Task>`.
//!
//! ## Cross-engine dependents
//!
//! A binode task in Phase Solitonic or Base waits on the result of one or
//! two `HashLife` nodes. It registers itself on the `HashLife` node's
//! dependents list as `Dependent::Binode { entry_idx, size_log2 }`. `HashLife`
//! sub-children registered during async descent of a `HashLife` node use
//! `Dependent::Node { idx, size_log2 }`. The `HashLife` `notify_dependents`
//! dispatches by variant, pushing to `bi_queue` or `hash_queue`
//! appropriately.
//!
//! Dependents-list and `waiting_cnt` synchronization mirror the `HashLife`
//! executor — see [`super::hashlife_executor`] module docs for the full state
//! machine. The bit-flag state machine on `n.status` is shared across both
//! engines.

mod recovery;
use recovery::PausedWork;

use super::{
    super::{
        LEAF_SIZE_LOG2, algorithm,
        hashtable::{BinodeCache, BinodeCacheRef, Idx, NodeStoreRef},
        sharded_statistics::{ExecutionStatistics, set_current_execution_stats, record_last_victim_steal, take_current_execution_stats, Ticks, record_task_duration, record_steal, MetricKind, record_status_claim_fail, record_status_claim_success, record_metric},
        spin::Spinner,
        status,
        streamlife::StreamLifeEngine,
    },
    common::{
        DependencyHandlingResult, HashProcessingData, ProcessingGuard, Task, WAITING_BIAS,
        handle_dependency, is_finished, update_node_async,
    },
    parking::{Parking, Search},
    processing::{ActiveWork, ProcessingData},
    task_queue::{TaskQueue, TaskStealer},
};
use crossbeam::{deque::Steal, sync::Parker};
use smallvec::{SmallVec, smallvec};
use std::{
    sync::atomic::{AtomicU8, AtomicU16, Ordering},
    thread,
};

const INITIAL_TASK_QUEUE_CAPACITY: usize = 32;

/// A unit of work representing a binode pair to be processed.
#[derive(Clone, Copy)]
pub struct BiTask {
    /// Index into the `BinodeCache` for this binode pair.
    pub entry_idx: Idx,
    /// Size (log2) of the nodes in this pair.
    pub size_log2: u32,
}

impl super::task_queue::TaskWord for BiTask {
    fn into_word(self) -> u64 {
        u64::from(self.entry_idx) | (u64::from(self.size_log2) << 32)
    }
    fn from_word(word: u64) -> Self {
        Self {
            entry_idx: word as u32,
            size_log2: (word >> 32) as u32,
        }
    }
}

/// Tagged dependent for a `HashLife` `QuadTreeNode` processed during a
/// `StreamLife` run. A `HashLife` node's dependents list (under `Dep =
/// Dependent`) can hold either kind of waiter:
/// - `Node`: another `HashLife` node (descended from a binode task) is waiting.
/// - `Binode`: a binode task is waiting (Phases Solitonic / Base).
///
/// The `size_log2` is stored on the variant because the dependent's level is
/// not always derivable from the dependency's: a binode in Phase S/B depends
/// on a `HashLife` node at the *same* level, while a `HashLife` child is at one
/// level below its parent.
#[derive(Clone, Copy)]
pub enum Dependent {
    Node { idx: Idx, size_log2: u32 },
    Binode { entry_idx: Idx, size_log2: u32 },
}

/// Phase tag for a `BiTask`'s state machine. Set on the first invocation
/// (Phase Entry) and read on every subsequent invocation to dispatch.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
enum BiPhase {
    /// First invocation; phase not yet decided.
    #[default]
    Entry,
    /// Two universes are provably non-interacting. Need async
    /// `update_node`-equivalent results for both `idx.0` and `idx.1`.
    Solitonic,
    /// Smallest recursive level. Universes merged synchronously; need async
    /// `update_node`-equivalent result for the merged node.
    Base,
    /// Standard recursive case: 9-then-4 binode children. State tracked via
    /// existing `mask9_waiting` / `mask4_waiting` masks (no cross-engine
    /// dependents involved).
    Recursive,
}

/// Owner-only state for the binode phase machine.
#[derive(Default)]
struct BiWork {
    /// Phase the task is currently in (see [`BiPhase`]).
    phase: BiPhase,
    /// Intermediate child node results for universe 0 (BESZEL).
    /// In Phase Base, `arr0[0]` holds the merged-universes node.
    arr0: [Idx; 9],
    /// Intermediate child node results for universe 1 (ULQOMA).
    arr1: [Idx; 9],
    /// Bitmask: bit `i` set if child pair `i` (among first 9) is not yet computed.
    /// Used in Phase Recursive only.
    mask9_waiting: u32,
    /// Bitmask: bit `i` set if child pair `i` (among first 4) is not yet computed.
    /// Used in Phase Recursive only.
    mask4_waiting: u32,
    /// Hash-result scratch for Phases Solitonic / Base.
    ///   Phase Solitonic: `hash_results`[0] = i1 (for idx.0), `hash_results`[1] = i2 (for idx.1).
    ///   Phase Base: `hash_results`[0] = i3 (for the merged node stored in arr0[0]).
    hash_results: [Idx; 2],
    /// Bitmask of pending `HashLife` results for Phases Solitonic / Base.
    /// Solitonic uses bits 0,1; Base uses bit 0 only.
    hash_mask: u8,
}

type BiProcessingData = ProcessingData<BiWork, BiTask>;

/// Parallel executor for `StreamLife`'s `update_binode` using work-stealing.
pub struct StreamLifeExecutor<'a> {
    engine: &'a StreamLifeEngine,
    biroot: (Idx, Idx),
    size_log2: u32,
}

impl<'a> StreamLifeExecutor<'a> {
    pub fn new(engine: &'a StreamLifeEngine, biroot: (Idx, Idx), size_log2: u32) -> Self {
        Self {
            engine,
            biroot,
            size_log2,
        }
    }

    pub fn run(&self, paused: Option<PausedWork>) -> Option<(Idx, Idx)> {
        let num_threads = self.engine.base.threads_cnt;
        let timer = std::time::Instant::now();
        let bicache = &self.engine.bicache;

        // Look up root entry
        let root_idx = bicache.entry(self.biroot);
        let root_status = bicache.get(root_idx).status();

        if is_finished(root_status) {
            return Some(bicache.get(root_idx).payload().get_value());
        }
        if paused.is_none() {
            assert!(start_processing_entry(bicache, root_idx, smallvec![]));
        } else {
            assert_eq!(root_status.load(Ordering::Relaxed), status::PENDING);
        }

        // Create worker queues and stealers for both task kinds.
        let mut bi_queues = Vec::with_capacity(num_threads);
        let mut bi_stealers = Vec::with_capacity(num_threads);
        let mut hash_queues = Vec::with_capacity(num_threads);
        let mut hash_stealers = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let bi_queue = TaskQueue::new(INITIAL_TASK_QUEUE_CAPACITY);
            let hash_queue = TaskQueue::new(INITIAL_TASK_QUEUE_CAPACITY);
            bi_stealers.push(bi_queue.stealer());
            hash_stealers.push(hash_queue.stealer());
            bi_queues.push(bi_queue);
            hash_queues.push(hash_queue);
        }

        let tasks = paused.map_or_else(
            || vec![ReadyTask::Bi(BiTask { entry_idx: root_idx, size_log2: self.size_log2 })],
            |paused| paused.tasks,
        );
        assert!(!tasks.is_empty(), "unfinished update has no runnable tasks");
        for (i, task) in tasks.into_iter().enumerate() {
            match task {
                ReadyTask::Bi(task) => bi_queues[i % num_threads].push(task),
                ReadyTask::Hash(task) => hash_queues[i % num_threads].push(task),
            }
        }

        let (parking, parkers) = Parking::new(num_threads);
        let mut total_stats = ExecutionStatistics::new();
        thread::scope(|scope| {
            let mut handles = Vec::with_capacity(num_threads);
            for (thread_idx, ((bi_queue, hash_queue), parker)) in bi_queues
                .into_iter()
                .zip(hash_queues)
                .zip(parkers)
                .enumerate()
            {
                let executor_thread = BiExecutorThread {
                    parking: &parking,
                    parker,
                    engine: self.engine,
                    bicache_ref: bicache.create_ref(thread_idx),
                    node_ref: self.engine.base.mem.create_ref(thread_idx),
                    root_status,
                    thread_idx,
                    bi_queue,
                    hash_queue,
                    bi_stealers: &bi_stealers,
                    hash_stealers: &hash_stealers,
                };
                handles.push(scope.spawn(move || executor_thread.run()));
            }

            for handle in handles {
                total_stats.merge_from(&handle.join().unwrap());
            }
        });

        if self.engine.base.mem.exceeds_load_factor() || bicache.exceeds_load_factor() {
            return None;
        }

        assert!(is_finished(root_status));
        println!("Time spent on streamlife executor: {:?}", timer.elapsed());
        println!(
            "Nodes count: {} / {}, BiCache count: {} / {}",
            self.engine.base.mem.len(),
            self.engine.base.mem.capacity(),
            bicache.len(),
            bicache.capacity()
        );
        #[cfg(feature = "statistics")]
        println!("{total_stats}");

        Some(bicache.get(root_idx).payload().get_value())
    }

    /// Drop orphaned `HashProcessingData<Dependent>` (`HashLife` nodes) and
    /// `BiProcessingData` (binode entries) on cancellation. Must be called
    /// from a single-threaded context after `thread::scope` has joined; only
    /// PENDING slots own a live box at that point.
    pub fn discard_pending(engine: &StreamLifeEngine) {
        // Binode entries
        let bicache = &engine.bicache;
        bicache.for_each_idx(|idx| {
            let entry = bicache.get(idx);
            let status = entry.status().load(Ordering::Relaxed);
            if status == status::PENDING {
                // SAFETY: PENDING owns the original Box pointer; all workers have joined.
                unsafe { drop(Box::from_raw(entry.payload().get_ptr::<BiProcessingData>())) };
                entry.status().store(status::NOT_STARTED, Ordering::Relaxed);
            }
        });
        // HashLife nodes processed asynchronously during this StreamLife run
        // can also be orphaned in PENDING state. Free their
        // `HashProcessingData<Dependent>` boxes.
        let mem = &engine.base.mem;
        mem.for_each_idx(|idx| {
            let n = mem.get(idx);
            let status = n.status.load(Ordering::Relaxed);
            if status == status::PENDING {
                // SAFETY: PENDING owns the original Box pointer; all workers have joined.
                unsafe { drop(Box::from_raw(n.cache.get_ptr::<HashProcessingData<Dependent>>())) };
                n.status.store(status::NOT_STARTED, Ordering::Relaxed);
            }
        });
    }
}

enum ChildResult {
    Ready((Idx, Idx)),
    Pending,
}

enum ReadyTask {
    Bi(BiTask),
    Hash(Task),
}

/// Per-thread worker for the `StreamLife` parallel executor.
///
/// Holds two deques (binode and `HashLife`) and processes work from either
/// kind, with a custom dual-queue fetch loop in [`Self::run`].
struct BiExecutorThread<'a> {
    parking: &'a Parking,
    parker: Parker,
    engine: &'a StreamLifeEngine,
    bicache_ref: BinodeCacheRef<'a>,
    node_ref: NodeStoreRef<'a, u64>,
    root_status: &'a AtomicU8,
    thread_idx: usize,
    bi_queue: TaskQueue<BiTask>,
    hash_queue: TaskQueue<Task>,
    bi_stealers: &'a [TaskStealer<BiTask>],
    hash_stealers: &'a [TaskStealer<Task>],
}

fn victim_probe_order(worker_count: usize, thread_idx: usize) -> Vec<usize> {
    let mut probe_order: Vec<_> = (0..worker_count).filter(|&i| i != thread_idx).collect();
    let mut shuffle_state = (thread_idx as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15);
    for i in (1..probe_order.len()).rev() {
        shuffle_state ^= shuffle_state << 13;
        shuffle_state ^= shuffle_state >> 7;
        shuffle_state ^= shuffle_state << 17;
        probe_order.swap(i, (shuffle_state % (i as u64 + 1)) as usize);
    }
    probe_order
}

struct SearchState {
    last_bi_victim: usize,
    last_hash_victim: usize,
    probe_order: Vec<usize>,
    probe_position: usize,
}

impl SearchState {
    fn new(worker_count: usize, thread_idx: usize) -> Self {
        Self {
            last_bi_victim: 0,
            last_hash_victim: 0,
            probe_order: victim_probe_order(worker_count, thread_idx),
            probe_position: 0,
        }
    }

    /// Try remembered foreign queues, then one complete pass in the worker's shuffled order.
    fn steal_active(&mut self, worker: &BiExecutorThread<'_>) -> Option<ReadyTask> {
        if self.last_bi_victim != worker.thread_idx {
            let bi = worker.try_steal_bi(self.last_bi_victim);
            record_last_victim_steal(&bi);
            if let Some(task) = bi {
                return Some(ReadyTask::Bi(task));
            }
        }
        if self.last_hash_victim != worker.thread_idx {
            let hash = worker.try_steal_hash(self.last_hash_victim);
            record_last_victim_steal(&hash);
            if let Some(task) = hash {
                return Some(ReadyTask::Hash(task));
            }
        }
        for _ in 0..self.probe_order.len() {
            let victim = self.probe_order[self.probe_position];
            self.probe_position += 1;
            if self.probe_position == self.probe_order.len() {
                self.probe_position = 0;
            }
            if let Some(task) = self.steal_from(worker, victim) {
                return Some(task);
            }
        }
        None
    }

    /// The idle captain checks completion, then local, remembered and cyclic foreign queues.
    fn search_as_captain(&mut self, worker: &BiExecutorThread<'_>) -> Search<ReadyTask> {
        if worker.cancelled() || is_finished(worker.root_status) {
            return Search::Stop;
        }
        if let Some(task) = worker.pop_local_task() {
            return Search::Work(task);
        }
        let bi = worker.try_steal_bi(self.last_bi_victim);
        record_last_victim_steal(&bi);
        if let Some(task) = bi {
            return Search::Work(ReadyTask::Bi(task));
        }
        let hash = worker.try_steal_hash(self.last_hash_victim);
        record_last_victim_steal(&hash);
        if let Some(task) = hash {
            return Search::Work(ReadyTask::Hash(task));
        }
        for offset in 1..worker.bi_stealers.len() {
            let victim = (worker.thread_idx + offset) % worker.bi_stealers.len();
            if let Some(task) = self.steal_from(worker, victim) {
                return Search::Work(task);
            }
        }
        Search::Empty
    }

    fn steal_from(&mut self, worker: &BiExecutorThread<'_>, victim: usize) -> Option<ReadyTask> {
        if let Some(task) = worker.try_steal_bi(victim) {
            self.last_bi_victim = victim;
            return Some(ReadyTask::Bi(task));
        }
        if let Some(task) = worker.try_steal_hash(victim) {
            self.last_hash_victim = victim;
            return Some(ReadyTask::Hash(task));
        }
        None
    }
}

impl BiExecutorThread<'_> {
    fn run(&self) -> ExecutionStatistics {
        let _stop_on_exit = self.parking.stop_on_exit();
        set_current_execution_stats();
        let mut search = SearchState::new(self.bi_stealers.len(), self.thread_idx);

        loop {
            if self.cancelled() {
                break;
            }
            let task = self.pop_local_task()
                .or_else(|| search.steal_active(self))
                .or_else(|| self.parking.search(self.thread_idx, &self.parker, || search.search_as_captain(self)));
            match task {
                Some(ReadyTask::Bi(task)) => self.timed_process_bi_task(task),
                Some(ReadyTask::Hash(task)) => self.timed_process_hash_task(task),
                None => break,
            }
            if is_finished(self.root_status) {
                break;
            }
        }
        take_current_execution_stats().unwrap()
    }

    fn cancelled(&self) -> bool {
        self.engine.base.mem.exceeds_load_factor() || self.bicache_ref.exceeds_load_factor()
    }

    fn pop_local_task(&self) -> Option<ReadyTask> {
        self.hash_queue
            .pop()
            .map(ReadyTask::Hash)
            .or_else(|| self.bi_queue.pop().map(ReadyTask::Bi))
    }

    fn timed_process_bi_task(&self, task: BiTask) {
        let start = Ticks::now();
        self.process_bi_task(task);
        record_task_duration(Ticks::now().elapsed_since(start));
    }

    fn timed_process_hash_task(&self, task: Task) {
        let start = Ticks::now();
        self.process_hash_task(task);
        record_task_duration(Ticks::now().elapsed_since(start));
    }

    fn try_steal_bi(&self, victim: usize) -> Option<BiTask> {
        loop {
            let result = self.bi_queue.steal_from(&self.bi_stealers[victim]);
            record_steal(&result);
            match result {
                Steal::Success(task) => return Some(task),
                Steal::Empty => return None,
                Steal::Retry => {}
            }
        }
    }

    fn try_steal_hash(&self, victim: usize) -> Option<Task> {
        loop {
            let result = self.hash_queue.steal_from(&self.hash_stealers[victim]);
            record_steal(&result);
            match result {
                Steal::Success(task) => return Some(task),
                Steal::Empty => return None,
                Steal::Retry => {},
            }
        }
    }

    /// Process a single binode task: drive its phase machine.
    fn process_bi_task(&self, task: BiTask) {
        let entry = self.bicache_ref.get(task.entry_idx);
        let status = entry.status();
        let mut guard = ProcessingGuard::new(status, MetricKind::ProcessTask);
        // SAFETY: ACTIVE keeps the payload alive and exclusively owns its work state.
        let data_ptr = unsafe { entry.payload().get_ptr::<BiProcessingData>() };
        let data = unsafe { &*data_ptr };
        let idx = entry.key();

        if let Some(result) = self.update_binode(task.entry_idx, idx, task.size_log2, unsafe { data.active_work() }) {
            guard.enter_finish_barrier(MetricKind::NotifyDep);
            let dependents = unsafe { data.take_dependents() };
            entry.payload().set_value(result);
            guard.publish_finished();
            // SAFETY: no payload access remains; retain the original Box pointer.
            unsafe { drop(Box::from_raw(data_ptr)) };
            self.notify_bi_dependents(dependents);
        }
    }

    /// Process a single `HashLife` task descended from a binode Phase S/B.
    /// Mirror of `HashLife`'s `process_task` but uses
    /// `HashProcessingData<Dependent>` so cross-engine waiters can register.
    fn process_hash_task(&self, task: Task) {
        let n = self.node_ref.get(task.idx);
        let mut guard = ProcessingGuard::new(&n.status, MetricKind::ProcessTask);
        // SAFETY: ACTIVE keeps the payload alive and exclusively owns its work state.
        let data_ptr = unsafe { n.cache.get_ptr::<HashProcessingData<Dependent>>() };
        let data = unsafe { &*data_ptr };
        let dep = Dependent::Node {
            idx: task.idx,
            size_log2: task.size_log2,
        };
        let parts = n.parts();
        let result = update_node_async(
            &self.node_ref,
            |task| self.hash_queue.push(task),
            self.engine.base.generations_per_update_log2.unwrap(),
            &task,
            parts,
            unsafe { data.active_work() },
            dep,
        );
        if let Some(result) = result {
            guard.enter_finish_barrier(MetricKind::NotifyDep);
            let dependents = unsafe { data.take_dependents() };
            n.cache.set_value(result);
            guard.publish_finished();
            // SAFETY: no payload access remains; retain the original Box pointer.
            unsafe { drop(Box::from_raw(data_ptr)) };
            self.notify_node_dependents(dependents);
        }
    }

    /// Compute binode result or yield, advancing the phase machine.
    ///
    /// On the first invocation, decides the phase (Solitonic / Base /
    /// Recursive) and falls through. On subsequent invocations, reads the
    /// stored phase and dispatches.
    ///
    /// Returns `Some(result)` when the task can be finalized, `None` when
    /// at least one dependency is still in flight (wake-up duty transferred
    /// via the `waiting_cnt` bias trick).
    fn update_binode(
        &self,
        parent_entry_idx: Idx,
        idx: (Idx, Idx),
        size_log2: u32,
        active: ActiveWork<'_, BiWork>,
    ) -> Option<(Idx, Idx)> {
        let data = &mut *active.work;
        let engine = self.engine;
        let gens_log2 = engine.base.generations_per_update_log2.unwrap();

        // === Phase Entry: first invocation, decide which phase to enter ===
        //
        // Invariant: every call into algorithm:: from this executor must go
        // through `self.node_ref` (a per-thread `NodeStoreRef`) so that
        // allocations land in this thread's chunk pool and free list. Calling
        // `engine.base.mem.find_or_create_*` directly funnels every worker
        // through shard 0 of the underlying `ConcurrentHashTable`, which races
        // on the bump pointer / free list and produces torn slot bodies.
        if data.phase == BiPhase::Entry {
            // is_solitonic is sync; it spins on node2lanes' status_extra.
            if algorithm::is_solitonic(&self.node_ref, &engine.base.blank_nodes, idx, size_log2)? {
                data.phase = BiPhase::Solitonic;
                data.hash_mask = 0b11; // need both i1, i2
            } else if size_log2 == LEAF_SIZE_LOG2 + 2 {
                data.phase = BiPhase::Base;
                // Synchronous: tree assembly only, no waits.
                let merged = algorithm::merge_universes(
                    &self.node_ref,
                    &engine.base.blank_nodes,
                    idx,
                    size_log2,
                );
                data.arr0[0] = merged;
                data.hash_mask = 0b1; // need i3
            } else {
                data.phase = BiPhase::Recursive;
                let both_stages = gens_log2 + 2 >= size_log2;
                let n0 = self.node_ref.get(idx.0);
                let n1 = self.node_ref.get(idx.1);
                if both_stages {
                    data.arr0 = algorithm::nine_children_overlapping(
                        &self.node_ref,
                        n0.nw,
                        n0.ne,
                        n0.sw,
                        n0.se,
                    );
                    data.arr1 = algorithm::nine_children_overlapping(
                        &self.node_ref,
                        n1.nw,
                        n1.ne,
                        n1.sw,
                        n1.se,
                    );
                    data.mask9_waiting = 0b1_1111_1111;
                } else {
                    data.arr0 = algorithm::nine_children_disjoint(
                        &self.node_ref,
                        n0.nw,
                        n0.ne,
                        n0.sw,
                        n0.se,
                        size_log2 - 1,
                    );
                    data.arr1 = algorithm::nine_children_disjoint(
                        &self.node_ref,
                        n1.nw,
                        n1.ne,
                        n1.sw,
                        n1.se,
                        size_log2 - 1,
                    );
                    // Single-stage: skip directly to arr4 (mask9 stays 0).
                }
            }
        }

        // Dispatch by phase.
        match data.phase {
            BiPhase::Entry => unreachable!("Entry should have been transitioned"),
            BiPhase::Solitonic => self.solitonic_phase(parent_entry_idx, idx, size_log2, active),
            BiPhase::Base => self.base_phase(parent_entry_idx, size_log2, active),
            BiPhase::Recursive => self.recursive_phase(parent_entry_idx, size_log2, active),
        }
    }

    /// Phase Solitonic: wait for `update_node_async`-equivalent of
    /// `idx.0` and `idx.1`, then assemble.
    fn solitonic_phase(
        &self,
        parent_entry_idx: Idx,
        idx: (Idx, Idx),
        size_log2: u32,
        active: ActiveWork<'_, BiWork>,
    ) -> Option<(Idx, Idx)> {
        let ActiveWork { work: data, waiting_cnt } = active;
        let targets = [idx.0, idx.1];
        let dep = Dependent::Binode {
            entry_idx: parent_entry_idx,
            size_log2,
        };

        if data.hash_mask != 0 {
            waiting_cnt.fetch_add(WAITING_BIAS, Ordering::Relaxed);
            for (b, target) in targets.iter().enumerate() {
                if data.hash_mask & (1 << b) == 0 {
                    continue;
                }
                let target_node = self.node_ref.get(*target);
                match handle_dependency(target_node, dep) {
                    DependencyHandlingResult::Ready => {
                        data.hash_mask &= !(1 << b);
                        data.hash_results[b] = target_node.cache.get_value();
                    }
                    DependencyHandlingResult::StartedByThisThread => {
                        waiting_cnt.fetch_add(1, Ordering::Relaxed);
                        self.hash_queue.push(Task::new(*target, size_log2));
                    }
                    DependencyHandlingResult::StartedByOtherThread => {
                        waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    }
                }
            }
            let prev = waiting_cnt.fetch_sub(WAITING_BIAS, Ordering::AcqRel);
            if data.hash_mask != 0 {
                if prev == WAITING_BIAS {
                    self.bi_queue.push(BiTask {
                        entry_idx: parent_entry_idx,
                        size_log2,
                    });
                }
                return None;
            }
        }

        self.finish_solitonic(idx, data.hash_results, size_log2)
    }

    fn finish_solitonic(&self, idx: (Idx, Idx), [i1, i2]: [Idx; 2], size_log2: u32) -> Option<(Idx, Idx)> {
        let engine = self.engine;
        let b = engine.base.blank_nodes.get(size_log2);
        let result = if idx.0 == b || idx.1 == b {
            let (i3, ind3) = if idx.0 == b { (i2, idx.1) } else { (i1, idx.0) };
            // Sync: lane query (kept synchronous in v1; node2lanes uses its
            // own spinner-on-status_extra for in-flight waits).
            let lanes =
                algorithm::node2lanes(&self.node_ref, &engine.base.blank_nodes, ind3, size_log2)?;
            let blank_child = engine.base.blank_nodes.get(size_log2 - 1);
            if lanes & 0xf0 != 0 {
                (blank_child, i3)
            } else {
                (i3, blank_child)
            }
        } else {
            (i1, i2)
        };
        Some(result)
    }

    /// Phase Base: wait for `update_node_async`-equivalent of the merged
    /// universe, then assemble.
    fn base_phase(
        &self,
        parent_entry_idx: Idx,
        size_log2: u32,
        active: ActiveWork<'_, BiWork>,
    ) -> Option<(Idx, Idx)> {
        let ActiveWork { work: data, waiting_cnt } = active;
        let engine = self.engine;
        let merged = data.arr0[0];
        let dep = Dependent::Binode {
            entry_idx: parent_entry_idx,
            size_log2,
        };

        if data.hash_mask != 0 {
            waiting_cnt.fetch_add(WAITING_BIAS, Ordering::Relaxed);
            // Only bit 0 is used for Phase Base.
            let target_node = self.node_ref.get(merged);
            match handle_dependency(target_node, dep) {
                DependencyHandlingResult::Ready => {
                    data.hash_mask &= !0b1;
                    data.hash_results[0] = target_node.cache.get_value();
                }
                DependencyHandlingResult::StartedByThisThread => {
                    waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    self.hash_queue.push(Task::new(merged, size_log2));
                }
                DependencyHandlingResult::StartedByOtherThread => {
                    waiting_cnt.fetch_add(1, Ordering::Relaxed);
                }
            }
            let prev = waiting_cnt.fetch_sub(WAITING_BIAS, Ordering::AcqRel);
            if data.hash_mask != 0 {
                if prev == WAITING_BIAS {
                    self.bi_queue.push(BiTask {
                        entry_idx: parent_entry_idx,
                        size_log2,
                    });
                }
                return None;
            }
        }

        let i3 = data.hash_results[0];
        let blank_child = engine.base.blank_nodes.get(size_log2 - 1);
        let result = if i3 == blank_child {
            (blank_child, blank_child)
        } else {
            // Sync: lane query on the merged node.
            let lanes =
                algorithm::node2lanes(&self.node_ref, &engine.base.blank_nodes, merged, size_log2)?;
            if lanes & 0xf0 != 0 {
                (blank_child, i3)
            } else {
                (i3, blank_child)
            }
        };
        Some(result)
    }

    // Independent universes already share HashLife's memoized results. Avoid a
    // second cache entry and intermediary task just to wait for those results.
    fn request_child(&self, key: (Idx, Idx), parent: BiTask, waiting_cnt: &AtomicU16) -> Option<ChildResult> {
        let size_log2 = parent.size_log2 - 1;
        if algorithm::is_solitonic(&self.node_ref, &self.engine.base.blank_nodes, key, size_log2)? {
            let dep = Dependent::Binode { entry_idx: parent.entry_idx, size_log2: parent.size_log2 };
            let mut results = [0; 2];
            let mut ready = true;
            for (i, idx) in [key.0, key.1].into_iter().enumerate() {
                let node = self.node_ref.get(idx);
                match handle_dependency(node, dep) {
                    DependencyHandlingResult::Ready => results[i] = node.cache.get_value(),
                    DependencyHandlingResult::StartedByThisThread => {
                        waiting_cnt.fetch_add(1, Ordering::Relaxed);
                        self.hash_queue.push(Task::new(idx, size_log2));
                        ready = false;
                    }
                    DependencyHandlingResult::StartedByOtherThread => {
                        waiting_cnt.fetch_add(1, Ordering::Relaxed);
                        ready = false;
                    }
                }
            }
            return if ready {
                Some(ChildResult::Ready(self.finish_solitonic(key, results, size_log2)?))
            } else {
                Some(ChildResult::Pending)
            };
        }
        let child_idx = self.bicache_ref.entry(key);
        match handle_bi_dependency(&self.engine.bicache, child_idx, parent.entry_idx, parent.size_log2) {
            BiDependencyResult::Ready => {
                Some(ChildResult::Ready(self.bicache_ref.get(child_idx).payload().get_value()))
            }
            BiDependencyResult::StartedByThisThread => {
                waiting_cnt.fetch_add(1, Ordering::Relaxed);
                self.bi_queue.push(BiTask { entry_idx: child_idx, size_log2 });
                Some(ChildResult::Pending)
            }
            BiDependencyResult::StartedByOtherThread => {
                waiting_cnt.fetch_add(1, Ordering::Relaxed);
                Some(ChildResult::Pending)
            }
        }
    }

    /// Phase Recursive: existing 9-then-4 binode children logic.
    fn recursive_phase(
        &self,
        parent_entry_idx: Idx,
        size_log2: u32,
        active: ActiveWork<'_, BiWork>,
    ) -> Option<(Idx, Idx)> {
        let ActiveWork { work: data, waiting_cnt } = active;

        // Stage 1: Wait for 9 overlapping children (if both_stages).
        if data.mask4_waiting == 0 && data.mask9_waiting != 0 {
            waiting_cnt.fetch_add(WAITING_BIAS, Ordering::Relaxed);
            for i in 0..9 {
                if data.mask9_waiting & (1 << i) == 0 {
                    continue;
                }
                let child_key = (data.arr0[i], data.arr1[i]);
                let parent = BiTask { entry_idx: parent_entry_idx, size_log2 };
                match self.request_child(child_key, parent, waiting_cnt)? {
                    ChildResult::Ready((a, b)) => {
                        data.mask9_waiting &= !(1 << i);
                        data.arr0[i] = a;
                        data.arr1[i] = b;
                    }
                    ChildResult::Pending => {}
                }
            }
            let prev = waiting_cnt.fetch_sub(WAITING_BIAS, Ordering::AcqRel);
            if data.mask9_waiting != 0 {
                if prev == WAITING_BIAS {
                    self.bi_queue.push(BiTask {
                        entry_idx: parent_entry_idx,
                        size_log2,
                    });
                }
                return None;
            }
        }

        // Transition: compute arr4 from the 9 results (or from disjoint
        // children when single-stage).
        if data.mask4_waiting == 0 {
            let arr40 = algorithm::four_children_overlapping(&self.node_ref, &data.arr0);
            let arr41 = algorithm::four_children_overlapping(&self.node_ref, &data.arr1);
            data.arr0[..4].copy_from_slice(&arr40);
            data.arr1[..4].copy_from_slice(&arr41);
            data.mask4_waiting = 0b1111;
        }

        // Stage 2: Wait for 4 final children.
        waiting_cnt.fetch_add(WAITING_BIAS, Ordering::Relaxed);
        for i in 0..4 {
            if data.mask4_waiting & (1 << i) == 0 {
                continue;
            }
            let child_key = (data.arr0[i], data.arr1[i]);
            let parent = BiTask { entry_idx: parent_entry_idx, size_log2 };
            match self.request_child(child_key, parent, waiting_cnt)? {
                ChildResult::Ready((a, b)) => {
                    data.mask4_waiting &= !(1 << i);
                    data.arr0[i] = a;
                    data.arr1[i] = b;
                }
                ChildResult::Pending => {}
            }
        }
        let prev = waiting_cnt.fetch_sub(WAITING_BIAS, Ordering::AcqRel);
        if data.mask4_waiting != 0 {
            if prev == WAITING_BIAS {
                self.bi_queue.push(BiTask {
                    entry_idx: parent_entry_idx,
                    size_log2,
                });
            }
            return None;
        }

        Some((
            self.node_ref.find_or_create_node(
                data.arr0[0],
                data.arr0[1],
                data.arr0[2],
                data.arr0[3],
            ),
            self.node_ref.find_or_create_node(
                data.arr1[0],
                data.arr1[1],
                data.arr1[2],
                data.arr1[3],
            ),
        ))
    }

    /// Notify dependents of a finished binode entry.
    ///
    /// Atomically decrements each dependent's `waiting_cnt`. The thread
    /// that drives the counter to zero re-queues the parent `BiTask`.
    fn notify_bi_dependents(&self, dependents: SmallVec<[BiTask; 2]>) {
        for dep in dependents {
            let entry = self.bicache_ref.get(dep.entry_idx);
            // SAFETY: an outstanding notification keeps the payload alive until
            // this decrement. Do not access it afterwards; another owner may free it.
            let data = unsafe { entry.payload().get_ptr::<BiProcessingData>() };
            let prev = unsafe { &(*data).waiting_cnt }.fetch_sub(1, Ordering::AcqRel);
            if prev == 1 {
                self.bi_queue.push(BiTask {
                    entry_idx: dep.entry_idx,
                    size_log2: dep.size_log2,
                });
            }
        }
    }

    /// Notify dependents of a finished `HashLife` node, dispatching by
    /// `Dependent` variant.
    ///
    /// Each variant's `size_log2` field carries the dependent's level
    /// directly — this decouples the notify path from any assumption about
    /// the relationship between dependency level and dependent level.
    fn notify_node_dependents(&self, dependents: SmallVec<[Dependent; 2]>) {
        for dep in dependents {
            match dep {
                Dependent::Node { idx, size_log2 } => {
                    let n = self.node_ref.get(idx);
                    // SAFETY: this notification keeps the payload alive until decrement.
                    let data = unsafe { n.cache.get_ptr::<HashProcessingData<Dependent>>() };
                    let prev = unsafe { &(*data).waiting_cnt }.fetch_sub(1, Ordering::AcqRel);
                    if prev == 1 {
                        self.hash_queue.push(Task::new(idx, size_log2));
                    }
                }
                Dependent::Binode {
                    entry_idx,
                    size_log2,
                } => {
                    let entry = self.bicache_ref.get(entry_idx);
                    // SAFETY: this notification keeps the payload alive until decrement.
                    let data = unsafe { entry.payload().get_ptr::<BiProcessingData>() };
                    let prev = unsafe { &(*data).waiting_cnt }.fetch_sub(1, Ordering::AcqRel);
                    if prev == 1 {
                        self.bi_queue.push(BiTask {
                            entry_idx,
                            size_log2,
                        });
                    }
                }
            }
        }
    }
}

/// Initialize a cache entry for processing by transitioning
/// `NOT_STARTED → PROCESSING → PENDING`.
///
/// Returns `true` if this thread successfully claimed the entry, `false` if another thread did.
///
/// Steps:
/// 1. CAS `NOT_STARTED → PROCESSING` claims the entry and erects an init
///    barrier (pushers spin while `PROCESSING` is observed).
/// 2. Allocate and install [`BiProcessingData`].
/// 3. `fetch_xor` flips `PROCESSING → PENDING` with Release semantics so
///    subsequent pushers observe the freshly-installed payload.
fn start_processing_entry(
    bicache: &BinodeCache,
    entry_idx: Idx,
    dependents: SmallVec<[BiTask; 2]>,
) -> bool {
    let entry = bicache.get(entry_idx);
    let status = entry.status();
    if status
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

    record_status_claim_success();
    let pd = BiProcessingData::new(dependents);
    entry.payload().set_ptr(Box::into_raw(Box::new(pd)));
    status.fetch_xor(status::PROCESSING | status::PENDING, Ordering::Release);
    true
}

/// Result of attempting to handle a binode dependency.
enum BiDependencyResult {
    /// Dependency already computed, result available in cache entry
    Ready,
    /// This thread successfully claimed the dependency for processing
    StartedByThisThread,
    /// Another thread is processing the dependency, we registered as dependent
    StartedByOtherThread,
}

/// Handle a binode dependency: check if ready, claim for processing, or
/// register as dependent.
///
/// Registration uses the [`status::DEPS_LOCK`] overlay bit, which can coexist
/// with both `PENDING` and `ACTIVE`. The pusher only waits during the brief
/// init / finish barriers (encoded as `PROCESSING`) or behind another
/// concurrent pusher.
///
/// `parent_entry_idx` and `parent_size_log2` identify the parent task that
/// depends on this child.
fn handle_bi_dependency(
    bicache: &BinodeCache,
    child_idx: Idx,
    parent_entry_idx: Idx,
    parent_size_log2: u32,
) -> BiDependencyResult {
    let child_entry = bicache.get(child_idx);
    let status = child_entry.status();

    let mut spinner = Spinner::new();
    loop {
        let cur = status.load(Ordering::Acquire);
        if cur & status::FINISHED != 0 {
            record_metric(spinner.count(), MetricKind::HandleBiDep);
            return BiDependencyResult::Ready;
        }
        if cur == status::NOT_STARTED {
            if start_processing_entry(
                bicache,
                child_idx,
                smallvec![BiTask {
                    entry_idx: parent_entry_idx,
                    size_log2: parent_size_log2,
                }],
            ) {
                record_metric(spinner.count(), MetricKind::HandleBiDep);
                return BiDependencyResult::StartedByThisThread;
            }
            // Lost the race; observe the new state on the next iteration.
            continue;
        }
        if cur & status::PROCESSING != 0 {
            spinner.spin();
            continue;
        }
        if cur & status::DEPS_LOCK != 0 {
            spinner.spin();
            continue;
        }
        let want = cur | status::DEPS_LOCK;
        if status
            .compare_exchange_weak(cur, want, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
        {
            // SAFETY: DEPS_LOCK keeps the payload alive and exclusively protects its list.
            unsafe {
                (&*child_entry.payload().get_ptr::<BiProcessingData>()).push_dependent(BiTask {
                    entry_idx: parent_entry_idx,
                    size_log2: parent_size_log2,
                });
            }
            status.fetch_and(!status::DEPS_LOCK, Ordering::Release);
            record_metric(spinner.count(), MetricKind::HandleBiDep);
            return BiDependencyResult::StartedByOtherThread;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::victim_probe_order;

    #[test]
    fn victim_probe_order_covers_other_workers_once() {
        for worker_count in [1, 2, 3, 4, 8, 16, 31, 64] {
            for thread_idx in 0..worker_count {
                let mut probe_order = victim_probe_order(worker_count, thread_idx);
                probe_order.sort_unstable();
                let other_workers: Vec<_> = (0..worker_count).filter(|&i| i != thread_idx).collect();
                assert_eq!(probe_order, other_workers);
            }
        }
    }
}
