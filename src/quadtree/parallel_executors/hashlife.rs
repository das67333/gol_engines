//! # Parallel Hashlife Executor
//!
//! Work-stealing parallel executor for the Hashlife algorithm.
//! Each thread has its own `Worker<Task>` queue; when a thread runs out of
//! work, it steals from other threads via `Stealer`. No global queue is used.

use super::{
    super::{
        hashlife::HashLifeEngine,
        hashtable::{Idx, NodeStore, NodeStoreRef},
        node::QuadTreeNode,
        sharded_statistics::{ExecutionStatistics, set_current_execution_stats, Ticks, record_task_duration, take_current_execution_stats, MetricKind},
        status,
    },
    common::{
        ProcessingData, ProcessingGuard, Task, TaskFetcher, is_finished, start_processing_node,
        update_node_async,
    },
};
use crossbeam::deque::{Stealer, Worker};
use smallvec::{SmallVec, smallvec};
use std::{sync::atomic::Ordering, thread};

/// Parallel executor for Hashlife algorithm using work-stealing.
pub struct HashLifeExecutor<'a, Meta: Default + Sync> {
    root: Idx,
    size_log2: u32,
    generations_log2: u32,
    mem: &'a NodeStore<Meta>,
}

impl<'a, Meta: Default + Sync> HashLifeExecutor<'a, Meta> {
    pub fn new(base: &'a HashLifeEngine<Meta>) -> Self {
        Self {
            root: base.root,
            size_log2: base.size_log2,
            generations_log2: base.generations_per_update_log2.unwrap(),
            mem: &base.mem,
        }
    }

    pub fn run(&self, num_threads: usize) -> Option<Idx> {
        let timer = std::time::Instant::now();
        let root_node = self.mem.get(self.root);

        // Reuse an already-computed root instead of queueing a task that can
        // never acquire the PENDING -> ACTIVE processing guard.
        if !start_processing_node::<Meta, Idx>(root_node, smallvec![]) {
            let root_status = root_node.status.load(Ordering::Acquire);
            assert!(
                root_status & status::FINISHED != 0,
                "root node has nonterminal status {root_status:#010b} before executor start"
            );
            println!("Time spent on hashlife executor: {:?}", timer.elapsed());
            println!("Nodes count: {} / {}", self.mem.len(), self.mem.capacity());
            return Some(root_node.cache.get_value());
        }

        // Create worker queues and stealers
        let mut queues = Vec::with_capacity(num_threads);
        let mut stealers = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let queue = Worker::new_lifo();
            let stealer = queue.stealer();
            queues.push(queue);
            stealers.push(stealer);
        }

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
        println!("Nodes count: {} / {}", self.mem.len(), self.mem.capacity());
        #[cfg(feature = "statistics")]
        println!("{total_stats}");

        Some(root_node.cache.get_value())
    }

    /// Drop `ProcessingData` boxes orphaned by cancellation. Must be called
    /// from a single-threaded context after `thread::scope` has joined; only
    /// PENDING slots own a live box at that point.
    fn free_orphaned_processing_data(&self) {
        self.mem.for_each_idx(|idx| {
            let n = self.mem.get(idx);
            let status = n.status.load(Ordering::Relaxed);
            if status == status::PENDING {
                let pd: &mut ProcessingData<Idx> = n.cache.get_ref();
                // SAFETY: produced by `Box::into_raw` in
                // `start_processing_node`; all workers have joined.
                unsafe { drop(Box::from_raw(std::ptr::from_mut::<ProcessingData<Idx>>(pd))) };
            }
        });
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

impl<Meta: Default + Sync> ExecutorThread<'_, Meta> {
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
        let data: &mut ProcessingData<Idx> = n.cache.get_ref();
        if let Some(result) = self.update_node(&task, n.parts(), data) {
            // Cross the finish barrier so pushers stop touching `data` and the
            // cache slot, then drain dependents, publish the value, and mark
            // the node FINISHED.
            guard.enter_finish_barrier(MetricKind::NotifyDep);
            let dependents = data.take_dependents();
            n.cache.set_value(result);
            guard.publish_finished();
            unsafe { drop(Box::from_raw(std::ptr::from_mut::<ProcessingData<Idx>>(data))) };
            self.notify_dependents(&task, &dependents);
        }
    }

    /// Compute node result by processing its children/dependencies.
    ///
    /// Returns `Some(result)` if computation completes, `None` if waiting for dependencies.
    fn update_node(
        &self,
        task: &Task,
        parts: [Idx; 4],
        data: &mut ProcessingData<Idx>,
    ) -> Option<Idx> {
        update_node_async(
            &self.mem,
            &self.queue,
            self.generations_log2,
            task,
            parts,
            data,
            task.idx,
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
    fn notify_dependents(&self, task: &Task, dependents: &SmallVec<[Idx; 2]>) {
        for &dependent in dependents {
            let n = self.mem.get(dependent);
            let dep_data: &ProcessingData<Idx> = n.cache.get_ref();
            let prev = dep_data.decrement_waiting_cnt();
            if prev == 1 {
                self.queue.push(Task::new(dependent, task.size_log2 + 1));
            }
        }
    }
}
