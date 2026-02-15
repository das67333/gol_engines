//! # Parallel StreamLife Executor
//!
//! Work-stealing parallel executor for the StreamLife algorithm's `update_binode` operation.
//! Follows the same architecture as `hashlife_executor`, but operates on pairs of nodes
//! `(NodeIdx, NodeIdx)` with state tracked in `StreamLifeCache`'s `CacheEntry`.
//!
//! ## Differences from HashLife Executor
//!
//! - Tasks are identified by `u32` indices into the `StreamLifeCache` (binode pairs)
//! - Processing data (`BiProcessingData`) is stored in the cache entry's payload union
//! - Solitonic and base cases are computed synchronously via `update_node_sync`
//! - Two parallel arrays (`arr0`, `arr1`) track the two universes

use super::{
    LEAF_SIZE_LOG2,
    hashlife_executor::{ProcessingGuard, TaskFetcher, is_finished},
    node::NodeIdx,
    status,
    streamlife::StreamLifeEngineAsync,
    streamlife_cache::StreamLifeCache,
};
use crossbeam::deque::{Stealer, Worker};
use smallvec::{SmallVec, smallvec};
use std::{
    hint, mem,
    sync::atomic::{AtomicU8, Ordering},
    thread,
};

/// A unit of work representing a binode pair to be processed.
#[derive(Clone, Copy)]
struct BiTask {
    /// Index into the StreamLifeCache for this binode pair.
    entry_idx: u32,
    /// Size (log2) of the nodes in this pair.
    size_log2: u32,
}

/// Temporary data allocated during binode processing.
///
/// Heap-allocated when processing starts, freed when entry reaches FINISHED state.
/// Stored via pointer in the cache entry's payload field.
#[derive(Default)]
struct BiProcessingData {
    /// Intermediate child node results for universe 0 (BESZEL).
    arr0: [NodeIdx; 9],
    /// Intermediate child node results for universe 1 (ULQOMA).
    arr1: [NodeIdx; 9],
    /// Bitmask: bit `i` set if child pair `i` (among first 9) is not yet computed.
    mask9_waiting: u32,
    /// Bitmask: bit `i` set if child pair `i` (among first 4) is not yet computed.
    mask4_waiting: u32,
    /// Count of dependencies still being computed. Entry can resume when this reaches 0.
    waiting_cnt: u32,
    /// Entries that registered as dependents of this entry.
    /// Notified when this entry finishes.
    dependents: SmallVec<[BiTask; 2]>,
}

/// Parallel executor for StreamLife's `update_binode` using work-stealing.
pub(super) struct StreamLifeExecutor<'a> {
    engine: &'a StreamLifeEngineAsync,
    biroot: (NodeIdx, NodeIdx),
    size_log2: u32,
}

impl<'a> StreamLifeExecutor<'a> {
    pub(super) fn new(
        engine: &'a StreamLifeEngineAsync,
        biroot: (NodeIdx, NodeIdx),
        size_log2: u32,
    ) -> Self {
        Self {
            engine,
            biroot,
            size_log2,
        }
    }

    pub(super) fn run(&self, num_threads: usize) -> (NodeIdx, NodeIdx) {
        let bicache = &self.engine.bicache;

        // Look up root entry
        let root_idx = bicache.entry(self.biroot);
        let root_status = &bicache.get(root_idx).status;

        // Create worker queues and stealers
        let mut queues = Vec::with_capacity(num_threads);
        let mut stealers = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let queue = Worker::new_lifo();
            let stealer = queue.stealer();
            queues.push(queue);
            stealers.push(stealer);
        }

        // Claim root entry and push initial task
        start_processing_entry(bicache, root_idx, smallvec![]);
        queues[0].push(BiTask {
            entry_idx: root_idx,
            size_log2: self.size_log2,
        });

        thread::scope(|scope| {
            for (thread_idx, queue) in queues.into_iter().enumerate() {
                let executor_thread = BiExecutorThread {
                    engine: self.engine,
                    root_status,
                    thread_idx,
                    queue,
                    stealers: &stealers,
                };
                scope.spawn(move || executor_thread.run());
            }
        });

        assert!(is_finished(root_status));
        println!(
            "(?) Nodes count: {}, BiCache count: {}",
            self.engine.base.mem.len(),
            bicache.len()
        );
        bicache.get(root_idx).get_value()
    }
}

/// Per-thread worker for the StreamLife parallel executor.
struct BiExecutorThread<'a> {
    engine: &'a StreamLifeEngineAsync,
    root_status: &'a AtomicU8,
    thread_idx: usize,
    queue: Worker<BiTask>,
    stealers: &'a [Stealer<BiTask>],
}

impl<'a> BiExecutorThread<'a> {
    fn run(&self) {
        let mut fetcher = TaskFetcher::new(
            self.thread_idx,
            &self.queue,
            self.stealers,
            || is_finished(self.root_status),
            || self.engine.base.mem.exceeds_load_factor(),
        );

        while let Some(task) = fetcher.fetch_task() {
            self.process_task(task);
        }
    }

    /// Process a single binode task.
    ///
    /// Flow:
    /// 1. Acquire PROCESSING status via `ProcessingGuard`
    /// 2. Call `update_binode` to compute result or identify dependencies
    /// 3. If result ready: store it, notify dependents, mark FINISHED
    /// 4. If dependencies needed: guard drops, status returns to PENDING
    fn process_task(&self, task: BiTask) {
        let bicache = &self.engine.bicache;
        let entry = bicache.get(task.entry_idx);
        let status = &entry.status;
        let mut guard = ProcessingGuard::new(status);
        let data: &mut BiProcessingData = unsafe { &mut *entry.get_ptr::<BiProcessingData>() };
        let idx = entry.key();

        if let Some(result) = self.update_binode(task.entry_idx, idx, task.size_log2, data) {
            entry.set_value(result);
            let mut dependents = SmallVec::new();
            mem::swap(&mut data.dependents, &mut dependents);
            guard.finish(); // Mark as FINISHED
            unsafe { drop(Box::from_raw(data as *mut BiProcessingData)) }; // Free BiProcessingData
            self.notify_dependents(dependents);
        }
        // If None: guard drops -> reverts to PENDING, task will be re-queued by a dependency
    }

    /// Compute binode result or identify dependencies.
    ///
    /// Returns `Some(result)` if computation completes, `None` if waiting for dependencies.
    ///
    /// Three cases:
    /// 1. **Solitonic**: Two universes are provably non-interacting. Compute each
    ///    independently via standard HashLife. Returns immediately.
    /// 2. **Base case** (`size_log2 == LEAF_SIZE_LOG2 + 2`): Merge universes and compute
    ///    via HashLife. Returns immediately.
    /// 3. **Recursive case**: Process 9+4 child binode pairs (same as HashLife structure
    ///    but with pairs).
    fn update_binode(
        &self,
        parent_entry_idx: u32,
        idx: (NodeIdx, NodeIdx),
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(NodeIdx, NodeIdx)> {
        let engine = self.engine;
        let bicache = &engine.bicache;

        // First entry into this task: check for synchronous fast-paths
        if data.mask4_waiting == 0 && data.mask9_waiting == 0 {
            // Solitonic: two universes don't interact, compute independently
            if engine.is_solitonic(idx, size_log2) {
                return Some(engine.compute_solitonic(idx, size_log2));
            }

            // Base case: merge universes and run standard HashLife
            if size_log2 == LEAF_SIZE_LOG2 + 2 {
                return Some(engine.compute_base_case(idx, size_log2));
            }

            // Recursive case: set up children for both universes
            let generations_log2 = engine.base.generations_per_update_log2.unwrap();
            let both_stages = generations_log2 + 2 >= size_log2;
            let n0 = engine.base.mem.get(idx.0);
            let n1 = engine.base.mem.get(idx.1);

            if both_stages {
                data.arr0 =
                    engine
                        .base
                        .nine_children_overlapping(n0.nw, n0.ne, n0.sw, n0.se);
                data.arr1 =
                    engine
                        .base
                        .nine_children_overlapping(n1.nw, n1.ne, n1.sw, n1.se);
                data.mask9_waiting = 0b1_1111_1111;
            } else {
                data.arr0 = engine.base.nine_children_disjoint(
                    n0.nw,
                    n0.ne,
                    n0.sw,
                    n0.se,
                    size_log2 - 1,
                );
                data.arr1 = engine.base.nine_children_disjoint(
                    n1.nw,
                    n1.ne,
                    n1.sw,
                    n1.se,
                    size_log2 - 1,
                );
                // Single-stage: skip directly to arr4 computation (mask9 stays 0)
            }
        }

        // Stage 1: Wait for 9 overlapping children (if both_stages)
        if data.mask4_waiting == 0 && data.mask9_waiting != 0 {
            let mut waiting_cnt = 0;
            for i in 0..9 {
                if data.mask9_waiting & (1 << i) == 0 {
                    continue;
                }
                let child_key = (data.arr0[i], data.arr1[i]);
                let child_idx = bicache.entry(child_key);

                match handle_bi_dependency(bicache, child_idx, parent_entry_idx, size_log2) {
                    BiDependencyResult::Ready => {
                        data.mask9_waiting &= !(1 << i);
                        let val = bicache.get(child_idx).get_value();
                        data.arr0[i] = val.0;
                        data.arr1[i] = val.1;
                    }
                    BiDependencyResult::StartedByThisThread => {
                        self.queue.push(BiTask {
                            entry_idx: child_idx,
                            size_log2: size_log2 - 1,
                        });
                        waiting_cnt += 1;
                    }
                    BiDependencyResult::StartedByOtherThread => {
                        waiting_cnt += 1;
                    }
                }
            }

            if data.mask9_waiting != 0 {
                data.waiting_cnt = waiting_cnt;
                return None;
            }
        }

        // Transition: compute arr4 from the 9 results (or from disjoint children)
        if data.mask4_waiting == 0 {
            let arr40 = engine.base.four_children_overlapping(&data.arr0);
            let arr41 = engine.base.four_children_overlapping(&data.arr1);
            data.arr0[..4].copy_from_slice(&arr40);
            data.arr1[..4].copy_from_slice(&arr41);
            data.mask4_waiting = 0b1111;
        }

        // Stage 2: Wait for 4 final children
        {
            let mut waiting_cnt = 0;
            for i in 0..4 {
                if data.mask4_waiting & (1 << i) == 0 {
                    continue;
                }
                let child_key = (data.arr0[i], data.arr1[i]);
                let child_idx = bicache.entry(child_key);

                match handle_bi_dependency(bicache, child_idx, parent_entry_idx, size_log2) {
                    BiDependencyResult::Ready => {
                        data.mask4_waiting &= !(1 << i);
                        let val = bicache.get(child_idx).get_value();
                        data.arr0[i] = val.0;
                        data.arr1[i] = val.1;
                    }
                    BiDependencyResult::StartedByThisThread => {
                        self.queue.push(BiTask {
                            entry_idx: child_idx,
                            size_log2: size_log2 - 1,
                        });
                        waiting_cnt += 1;
                    }
                    BiDependencyResult::StartedByOtherThread => {
                        waiting_cnt += 1;
                    }
                }
            }

            if data.mask4_waiting != 0 {
                data.waiting_cnt = waiting_cnt;
                return None;
            }
        }

        // Assemble final result from the 4 completed children
        Some((
            engine
                .base
                .mem
                .find_or_create_node(data.arr0[0], data.arr0[1], data.arr0[2], data.arr0[3]),
            engine
                .base
                .mem
                .find_or_create_node(data.arr1[0], data.arr1[1], data.arr1[2], data.arr1[3]),
        ))
    }

    /// Notify dependent entries that this dependency has completed.
    ///
    /// For each dependent:
    /// 1. Acquire PROCESSING status on the dependent's entry
    /// 2. Decrement its `waiting_cnt`
    /// 3. If `waiting_cnt` reaches 0, re-queue for processing
    fn notify_dependents(&self, dependents: SmallVec<[BiTask; 2]>) {
        let bicache = &self.engine.bicache;
        for dep in dependents {
            let entry = bicache.get(dep.entry_idx);
            let status = &entry.status;
            let waiting_cnt = {
                let _guard = ProcessingGuard::new(status);
                let dep_data: &mut BiProcessingData =
                    unsafe { &mut *entry.get_ptr::<BiProcessingData>() };
                dep_data.waiting_cnt -= 1;
                dep_data.waiting_cnt
            };
            if waiting_cnt == 0 {
                self.queue.push(BiTask {
                    entry_idx: dep.entry_idx,
                    size_log2: dep.size_log2,
                });
            }
        }
    }
}

/// Initialize a cache entry for processing by transitioning NOT_STARTED -> PROCESSING -> PENDING.
///
/// Returns `true` if this thread successfully claimed the entry, `false` if another thread did.
///
/// Steps:
/// 1. CAS(NOT_STARTED -> PROCESSING) to claim the entry
/// 2. Allocate and store BiProcessingData
/// 3. Store PENDING status (entry ready to be processed)
fn start_processing_entry(
    bicache: &StreamLifeCache,
    entry_idx: u32,
    dependents: SmallVec<[BiTask; 2]>,
) -> bool {
    let entry = bicache.get(entry_idx);
    let status = &entry.status;
    if status
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

    let pd = BiProcessingData {
        dependents,
        ..Default::default()
    };
    entry.set_ptr(Box::into_raw(Box::new(pd)));
    status.store(status::PENDING, Ordering::Release);
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

/// Handle a binode dependency: check if ready, claim for processing, or register as dependent.
///
/// The `parent_entry_idx` and `parent_size_log2` identify the parent task that depends on this child.
fn handle_bi_dependency(
    bicache: &StreamLifeCache,
    child_idx: u32,
    parent_entry_idx: u32,
    parent_size_log2: u32,
) -> BiDependencyResult {
    let child_entry = bicache.get(child_idx);
    let status = &child_entry.status;
    let status_value = status.load(Ordering::Acquire);

    if status_value == status::FINISHED {
        return BiDependencyResult::Ready;
    }

    if status_value == status::NOT_STARTED
        && start_processing_entry(
            bicache,
            child_idx,
            smallvec![BiTask {
                entry_idx: parent_entry_idx,
                size_log2: parent_size_log2,
            }],
        )
    {
        return BiDependencyResult::StartedByThisThread;
    }

    // Entry is being processed by another thread (or just claimed above by a racing thread).
    // Spin until we can register as dependent.
    loop {
        match status.compare_exchange_weak(
            status::PENDING,
            status::PROCESSING,
            Ordering::Acquire,
            Ordering::Acquire,
        ) {
            Ok(_) => {
                let child_data: &mut BiProcessingData =
                    unsafe { &mut *child_entry.get_ptr::<BiProcessingData>() };
                child_data.dependents.push(BiTask {
                    entry_idx: parent_entry_idx,
                    size_log2: parent_size_log2,
                });
                status.store(status::PENDING, Ordering::Release);
                return BiDependencyResult::StartedByOtherThread;
            }
            Err(status::FINISHED) => return BiDependencyResult::Ready,
            Err(status::PROCESSING) => {
                while status.load(Ordering::Relaxed) == status::PROCESSING {
                    hint::spin_loop()
                }
            }
            Err(value) => panic!("Unexpected status in handle_bi_dependency: {}", value),
        }
    }
}
