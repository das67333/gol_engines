//! # Parallel StreamLife Executor
//!
//! Work-stealing parallel executor for the StreamLife algorithm's
//! `update_binode` operation. Mirrors the architecture of
//! `hashlife_executor`, but operates on pairs of nodes `(Idx, Idx)` with
//! state tracked in `BinodeCache`'s `CacheEntry`.
//!
//! ## Differences from HashLife Executor
//!
//! - Tasks are identified by `u32` indices into the `BinodeCache`
//!   (binode pairs).
//! - Processing data (`BiProcessingData`) is stored in the cache entry's
//!   payload union.
//! - Solitonic and base cases are computed synchronously via
//!   `update_node_sync`.
//! - Two parallel arrays (`arr0`, `arr1`) track the two universes.
//!
//! ## Concurrency model
//!
//! The entry's `status` is an owner-exclusive lock for `BiProcessingData`.
//! Dependent registration and dependency-completion notification run
//! lock-free via
//! [`DepHead`](super::dep_stack::DepHead) and `CacheEntry::waiting_cnt`,
//! both living on the permanent cache entry itself. See the
//! [`hashlife_executor`](super::hashlife_executor) module documentation for
//! the full bias / publish-ordering protocol — StreamLife follows it
//! verbatim.

use super::{
    LEAF_SIZE_LOG2, algorithm,
    dep_stack::{self, DepState, PushResult},
    hashlife_executor::{ProcessingGuard, TaskFetcher, is_finished},
    hashtable::{BinodeCache, BinodeCacheRef, CacheEntry, Idx},
    sharded_statistics::*,
    status,
    streamlife::StreamLifeEngine,
};
use crossbeam::deque::{Stealer, Worker};
use std::{
    sync::atomic::{AtomicU8, Ordering},
    thread,
};

/// A unit of work representing a binode pair to be processed.
#[derive(Clone, Copy)]
struct BiTask {
    /// Index into the BinodeCache for this binode pair.
    entry_idx: Idx,
    /// Size (log2) of the nodes in this pair.
    size_log2: u32,
}

/// Temporary data allocated during binode processing.
///
/// Heap-allocated when processing starts, freed when the entry reaches
/// `FINISHED`. These fields are **owner-private**: only the thread that
/// holds `PROCESSING` on the entry ever reads or writes them.
/// `waiting_cnt` and the dependents list live on the `CacheEntry`
/// directly (see [`CacheEntry::waiting_cnt`] and
/// [`CacheEntry::dependents_head`](super::hashtable::CacheEntry)) so that
/// they are safe to touch without locks.
#[derive(Default)]
struct BiProcessingData {
    /// Intermediate child node results for universe 0 (BESZEL).
    arr0: [Idx; 9],
    /// Intermediate child node results for universe 1 (ULQOMA).
    arr1: [Idx; 9],
    /// Bitmask: bit `i` set if child pair `i` (among first 9) is not yet computed.
    mask9_waiting: u32,
    /// Bitmask: bit `i` set if child pair `i` (among first 4) is not yet computed.
    mask4_waiting: u32,
}

/// Parallel executor for StreamLife's `update_binode` using work-stealing.
pub(super) struct StreamLifeExecutor<'a> {
    engine: &'a StreamLifeEngine,
    biroot: (Idx, Idx),
    size_log2: u32,
}

impl<'a> StreamLifeExecutor<'a> {
    pub(super) fn new(engine: &'a StreamLifeEngine, biroot: (Idx, Idx), size_log2: u32) -> Self {
        Self {
            engine,
            biroot,
            size_log2,
        }
    }

    pub(super) fn run(&self, num_threads: usize) -> Option<(Idx, Idx)> {
        let timer = std::time::Instant::now();
        let bicache = &self.engine.bicache;

        // Look up root entry
        let root_idx = bicache.entry(self.biroot);
        let root_status = bicache.get(root_idx).status();

        // Create worker queues and stealers
        let mut queues = Vec::with_capacity(num_threads);
        let mut stealers = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let queue = Worker::new_lifo();
            let stealer = queue.stealer();
            queues.push(queue);
            stealers.push(stealer);
        }

        // Claim root entry and push initial task. The root has no parent
        // dependent.
        let claimed = start_processing_entry(bicache.get(root_idx), None);
        assert!(claimed, "root must be NOT_STARTED");
        queues[0].push(BiTask {
            entry_idx: root_idx,
            size_log2: self.size_log2,
        });

        let mut total_stats = ExecutionStatistics::new();
        thread::scope(|scope| {
            let mut handles = Vec::with_capacity(num_threads);
            for (thread_idx, queue) in queues.into_iter().enumerate() {
                let executor_thread = BiExecutorThread {
                    engine: self.engine,
                    bicache_ref: bicache.create_ref(thread_idx),
                    root_status,
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

        if self.engine.base.mem.exceeds_load_factor() || bicache.exceeds_load_factor() {
            return None;
        }

        assert!(is_finished(root_status));
        println!("Time spent on streamlife executor: {:?}", timer.elapsed());
        println!(
            "Nodes count: {}, BiCache count: {}",
            self.engine.base.mem.len(),
            bicache.len()
        );
        println!("{total_stats}");

        Some(bicache.get(root_idx).payload.get_value())
    }
}

/// Per-thread worker for the StreamLife parallel executor.
struct BiExecutorThread<'a> {
    engine: &'a StreamLifeEngine,
    bicache_ref: BinodeCacheRef<'a>,
    root_status: &'a AtomicU8,
    thread_idx: usize,
    queue: Worker<BiTask>,
    stealers: &'a [Stealer<BiTask>],
}

impl<'a> BiExecutorThread<'a> {
    fn run(&self) -> ExecutionStatistics {
        let mut fetcher = TaskFetcher::new(
            self.thread_idx,
            &self.queue,
            self.stealers,
            || is_finished(self.root_status),
            || self.engine.base.mem.exceeds_load_factor() || self.bicache_ref.exceeds_load_factor(),
        );
        set_current_execution_stats();

        while let Some(task) = fetcher.fetch_task() {
            let start = Ticks::now();
            self.process_task(task);
            record_task_duration(Ticks::now().elapsed_since(start));
        }

        take_current_execution_stats().unwrap()
    }

    /// Process a single binode task.
    ///
    /// Flow mirrors `hashlife_executor::ExecutorThread::process_task`:
    /// 1. Acquire PROCESSING status on the entry.
    /// 2. Add owner bias (`waiting_cnt += 1`).
    /// 3. Call `update_binode` to compute result or identify dependencies.
    /// 4. If result ready: publish, close dependents stack, mark FINISHED,
    ///    free `BiProcessingData`, notify dependents.
    /// 5. If still waiting: drop guard (back to PENDING), release bias;
    ///    self-re-enqueue if that brought the counter to zero.
    fn process_task(&self, task: BiTask) {
        let entry = self.bicache_ref.get(task.entry_idx);
        let status = entry.status();
        let mut guard = ProcessingGuard::new(status, MetricKind::ProcessTask);
        let data: &mut BiProcessingData = entry.payload.get_ref();
        let idx = entry.key();

        entry.waiting_cnt.fetch_add(1, Ordering::Relaxed);

        if let Some(result) = self.update_binode(task.entry_idx, idx, task.size_log2, data) {
            entry.payload.set_value(result);
            let drained = entry.dependents_head.close();
            guard.finish(); // PROCESSING -> FINISHED (Release)
            // SAFETY: See `hashlife_executor::process_task`.
            unsafe { drop(Box::from_raw(data as *mut BiProcessingData)) };
            self.drain_and_notify(drained, task.size_log2 + 1);
        } else {
            drop(guard);
            let prev = entry.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
            if prev == 1 {
                self.queue.push(task);
            }
        }
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
        parent_entry_idx: Idx,
        idx: (Idx, Idx),
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let engine = self.engine;

        // First entry into this task: check for synchronous fast-paths.
        if data.mask4_waiting == 0 && data.mask9_waiting == 0 {
            // Solitonic: two universes don't interact, compute independently
            if algorithm::is_solitonic(&engine.base.mem, &engine.base.blank_nodes, idx, size_log2) {
                return Some(algorithm::compute_solitonic(
                    &engine.base.mem,
                    &engine.base.blank_nodes,
                    self.engine.base.generations_per_update_log2.unwrap(),
                    idx,
                    size_log2,
                ));
            }

            // Base case: merge universes and run standard HashLife
            if size_log2 == LEAF_SIZE_LOG2 + 2 {
                return Some(algorithm::compute_base_case(
                    &engine.base.mem,
                    &engine.base.blank_nodes,
                    self.engine.base.generations_per_update_log2.unwrap(),
                    idx,
                    size_log2,
                ));
            }

            // Recursive case: set up children for both universes
            let generations_log2 = engine.base.generations_per_update_log2.unwrap();
            let both_stages = generations_log2 + 2 >= size_log2;
            let n0 = engine.base.mem.get(idx.0);
            let n1 = engine.base.mem.get(idx.1);

            if both_stages {
                data.arr0 = algorithm::nine_children_overlapping(
                    &engine.base.mem,
                    n0.nw,
                    n0.ne,
                    n0.sw,
                    n0.se,
                );
                data.arr1 = algorithm::nine_children_overlapping(
                    &engine.base.mem,
                    n1.nw,
                    n1.ne,
                    n1.sw,
                    n1.se,
                );
                data.mask9_waiting = 0b1_1111_1111;
            } else {
                data.arr0 = algorithm::nine_children_disjoint(
                    &engine.base.mem,
                    n0.nw,
                    n0.ne,
                    n0.sw,
                    n0.se,
                    size_log2 - 1,
                );
                data.arr1 = algorithm::nine_children_disjoint(
                    &engine.base.mem,
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
            let parent_entry = self.bicache_ref.get(parent_entry_idx);
            for i in 0..9 {
                if data.mask9_waiting & (1 << i) == 0 {
                    continue;
                }
                let child_key = (data.arr0[i], data.arr1[i]);
                let child_idx = self.bicache_ref.entry(child_key);

                match handle_bi_dependency_and_track(
                    &engine.bicache,
                    parent_entry,
                    child_idx,
                    parent_entry_idx,
                ) {
                    BiDependencyResult::Ready => {
                        data.mask9_waiting &= !(1 << i);
                        let val = self.bicache_ref.get(child_idx).payload.get_value();
                        data.arr0[i] = val.0;
                        data.arr1[i] = val.1;
                    }
                    BiDependencyResult::StartedByThisThread => {
                        self.queue.push(BiTask {
                            entry_idx: child_idx,
                            size_log2: size_log2 - 1,
                        });
                    }
                    BiDependencyResult::StartedByOtherThread => {}
                }
            }

            if data.mask9_waiting != 0 {
                return None;
            }
        }

        // Transition: compute arr4 from the 9 results (or from disjoint children)
        if data.mask4_waiting == 0 {
            let arr40 = algorithm::four_children_overlapping(&engine.base.mem, &data.arr0);
            let arr41 = algorithm::four_children_overlapping(&engine.base.mem, &data.arr1);
            data.arr0[..4].copy_from_slice(&arr40);
            data.arr1[..4].copy_from_slice(&arr41);
            data.mask4_waiting = 0b1111;
        }

        // Stage 2: Wait for 4 final children
        {
            let parent_entry = self.bicache_ref.get(parent_entry_idx);
            for i in 0..4 {
                if data.mask4_waiting & (1 << i) == 0 {
                    continue;
                }
                let child_key = (data.arr0[i], data.arr1[i]);
                let child_idx = self.bicache_ref.entry(child_key);

                match handle_bi_dependency_and_track(
                    &engine.bicache,
                    parent_entry,
                    child_idx,
                    parent_entry_idx,
                ) {
                    BiDependencyResult::Ready => {
                        data.mask4_waiting &= !(1 << i);
                        let val = self.bicache_ref.get(child_idx).payload.get_value();
                        data.arr0[i] = val.0;
                        data.arr1[i] = val.1;
                    }
                    BiDependencyResult::StartedByThisThread => {
                        self.queue.push(BiTask {
                            entry_idx: child_idx,
                            size_log2: size_log2 - 1,
                        });
                    }
                    BiDependencyResult::StartedByOtherThread => {}
                }
            }

            if data.mask4_waiting != 0 {
                return None;
            }
        }

        // Assemble final result from the 4 completed children
        Some((
            engine.base.mem.find_or_create_node(
                data.arr0[0],
                data.arr0[1],
                data.arr0[2],
                data.arr0[3],
            ),
            engine.base.mem.find_or_create_node(
                data.arr1[0],
                data.arr1[1],
                data.arr1[2],
                data.arr1[3],
            ),
        ))
    }

    /// Walk the drained dependents chain produced by `DepHead::close` and
    /// notify each dependent. A dependent whose `waiting_cnt` reaches zero is
    /// re-enqueued.
    fn drain_and_notify(&self, drained: DepState, dep_size_log2: u32) {
        dep_stack::drain(drained, |dep_idx| {
            let dep_entry = self.bicache_ref.get(dep_idx);
            let prev = dep_entry.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
            if prev == 1 {
                self.queue.push(BiTask {
                    entry_idx: dep_idx,
                    size_log2: dep_size_log2,
                });
            }
            record_metric(0, MetricKind::NotifyDep);
        });
    }
}

/// Initialize a cache entry for processing by transitioning NOT_STARTED -> PROCESSING -> PENDING.
///
/// Returns `true` if this thread successfully claimed the entry, `false` if
/// another thread did.
fn start_processing_entry(entry: &CacheEntry, initial_parent: Option<Idx>) -> bool {
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
    let pd = Box::into_raw(Box::new(BiProcessingData::default()));
    entry.payload.set_ptr(pd);
    if let Some(parent_idx) = initial_parent {
        let res = entry.dependents_head.push(parent_idx);
        debug_assert!(matches!(res, PushResult::Pushed));
    }
    status.store(status::PENDING, Ordering::Release);
    true
}

/// Result of attempting to handle a binode dependency.
enum BiDependencyResult {
    /// Dependency already computed, result available in cache entry.
    Ready,
    /// This thread successfully claimed the dependency for processing.
    StartedByThisThread,
    /// Another thread is processing the dependency; we registered as dependent.
    StartedByOtherThread,
}

/// Handle a binode dependency and update the parent's `waiting_cnt`.
///
/// See
/// [`hashlife_executor::handle_dependency_and_track`](super::hashlife_executor)
/// for the full ordering/undo argument; this is the binode mirror.
fn handle_bi_dependency_and_track(
    bicache: &BinodeCache,
    parent_entry: &CacheEntry,
    child_idx: Idx,
    parent_entry_idx: Idx,
) -> BiDependencyResult {
    let child_entry = bicache.get(child_idx);

    // Fast path: child already done.
    if is_finished(child_entry.status()) {
        return BiDependencyResult::Ready;
    }

    parent_entry.waiting_cnt.fetch_add(1, Ordering::Relaxed);

    let result = register_as_dependent(child_entry, parent_entry_idx);
    if matches!(result, BiDependencyResult::Ready) {
        parent_entry.waiting_cnt.fetch_sub(1, Ordering::Relaxed);
    }
    result
}

fn register_as_dependent(child: &CacheEntry, parent_entry_idx: Idx) -> BiDependencyResult {
    loop {
        let status_value = child.status().load(Ordering::Acquire);
        match status_value {
            status::FINISHED => return BiDependencyResult::Ready,
            status::NOT_STARTED => {
                if start_processing_entry(child, Some(parent_entry_idx)) {
                    return BiDependencyResult::StartedByThisThread;
                }
                // CAS lost; re-read status and retry.
            }
            status::PROCESSING | status::PENDING => {
                match child.dependents_head.push(parent_entry_idx) {
                    PushResult::Pushed => {
                        record_metric(0, MetricKind::HandleBiDep);
                        return BiDependencyResult::StartedByOtherThread;
                    }
                    PushResult::Closed => return BiDependencyResult::Ready,
                }
            }
            other => panic!("unexpected status {other}"),
        }
    }
}
