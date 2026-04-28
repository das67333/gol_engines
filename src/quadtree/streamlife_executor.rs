//! # Parallel StreamLife Executor
//!
//! Work-stealing parallel executor for the StreamLife algorithm's `update_binode` operation.
//! Follows the same architecture as `hashlife_executor`, but operates on pairs of nodes
//! `(Idx, Idx)` with state tracked in `BinodeCache`'s `CacheEntry`.
//!
//! ## Differences from HashLife Executor
//!
//! - Tasks are identified by `u32` indices into the `BinodeCache` (binode pairs)
//! - Processing data (`BiProcessingData`) is stored in the cache entry's payload union
//! - Solitonic and base cases are computed synchronously via `update_node_sync`
//! - Two parallel arrays (`arr0`, `arr1`) track the two universes
//!
//! Dependents-list and `waiting_cnt` synchronization mirror the HashLife
//! executor — see [`super::hashlife_executor`] module docs for the full state
//! machine.

use super::{
    LEAF_SIZE_LOG2, algorithm,
    hashlife_executor::{ProcessingGuard, TaskFetcher, is_finished},
    hashtable::{BinodeCache, BinodeCacheRef, Idx},
    sharded_statistics::*,
    spin::Spinner,
    status,
    streamlife::StreamLifeEngine,
};
use crossbeam::deque::{Stealer, Worker};
use smallvec::{SmallVec, smallvec};
use std::{
    mem,
    sync::atomic::{AtomicU8, AtomicU16, Ordering},
    thread,
};

/// Bias added to `waiting_cnt` while the owner is scanning children. See
/// [`super::hashlife_executor`] for the full rationale.
const WAITING_BIAS: u16 = 1 << 15;

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
/// Heap-allocated when processing starts, freed when entry reaches FINISHED state.
/// Stored via pointer in the cache entry's payload field.
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
    /// Count of dependencies still being computed. The entry resumes when
    /// this reaches 0. Manipulated lock-free with the bias trick.
    waiting_cnt: AtomicU16,
    /// Entries that registered as dependents of this entry. Mutated by the
    /// owner exclusively during the init / finish barriers, and by pushers
    /// in parallel under [`status::DEPS_LOCK`].
    dependents: SmallVec<[BiTask; 2]>,
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
        let root_status = &bicache.get(root_idx).status();

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
            // The base `NodeStore` carries no orphaned boxes: StreamLife
            // drives it via `update_node_sync`, never via async PROCESSING.
            self.free_orphaned_bi_processing_data();
            return None;
        }

        assert!(is_finished(root_status));
        println!("Time spent on streamlife executor: {:?}", timer.elapsed());
        println!(
            "Nodes count: {}, BiCache count: {}",
            self.engine.base.mem.len(),
            bicache.len()
        );
        #[cfg(feature = "statistics")]
        println!("{total_stats}");

        Some(bicache.get(root_idx).payload.get_value())
    }

    /// Binode-cache analogue of
    /// [`HashLifeExecutor::free_orphaned_processing_data`].
    fn free_orphaned_bi_processing_data(&self) {
        let bicache = &self.engine.bicache;
        for idx in 0..bicache.capacity() {
            let entry = bicache.get(idx as Idx);
            let status = entry.status().load(Ordering::Relaxed);
            if status == status::PENDING {
                let pd: &mut BiProcessingData = entry.payload.get_ref();
                // SAFETY: produced by `Box::into_raw` in
                // `start_processing_entry`; all workers have joined.
                unsafe { drop(Box::from_raw(pd as *mut BiProcessingData)) };
            }
        }
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
            || {
                self.engine.base.mem.exceeds_load_factor()
                    || self.bicache_ref.exceeds_load_factor()
            },
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
    /// Flow:
    /// 1. Acquire owner-mutex by transitioning `PENDING → ACTIVE`.
    /// 2. Call `update_binode` to compute the result or register dependencies.
    /// 3. If a result is ready: cross the finish barrier (`ACTIVE → PROCESSING`
    ///    once `DEPS_LOCK` clears), drain dependents, publish the value,
    ///    transition to `FINISHED`, and notify dependents.
    /// 4. Otherwise: guard drop transitions `ACTIVE → PENDING` while
    ///    preserving any in-flight `DEPS_LOCK`.
    fn process_task(&self, task: BiTask) {
        let entry = self.bicache_ref.get(task.entry_idx);
        let status = entry.status();
        let mut guard = ProcessingGuard::new(status, MetricKind::ProcessTask);
        let data: &mut BiProcessingData = entry.payload.get_ref();
        let idx = entry.key();

        if let Some(result) = self.update_binode(task.entry_idx, idx, task.size_log2, data) {
            guard.enter_finish_barrier(MetricKind::NotifyDep);
            let mut dependents = SmallVec::new();
            mem::swap(&mut data.dependents, &mut dependents);
            entry.payload.set_value(result);
            guard.publish_finished();
            unsafe { drop(Box::from_raw(data as *mut BiProcessingData)) };
            self.notify_dependents(dependents);
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

        // First entry into this task: check for synchronous fast-paths
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
            data.waiting_cnt
                .fetch_add(WAITING_BIAS, Ordering::Relaxed);
            for i in 0..9 {
                if data.mask9_waiting & (1 << i) == 0 {
                    continue;
                }
                let child_key = (data.arr0[i], data.arr1[i]);
                let child_idx = self.bicache_ref.entry(child_key);

                match handle_bi_dependency(&engine.bicache, child_idx, parent_entry_idx, size_log2)
                {
                    BiDependencyResult::Ready => {
                        data.mask9_waiting &= !(1 << i);
                        let val = self.bicache_ref.get(child_idx).payload.get_value();
                        data.arr0[i] = val.0;
                        data.arr1[i] = val.1;
                    }
                    BiDependencyResult::StartedByThisThread => {
                        data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                        self.queue.push(BiTask {
                            entry_idx: child_idx,
                            size_log2: size_log2 - 1,
                        });
                    }
                    BiDependencyResult::StartedByOtherThread => {
                        data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    }
                }
            }
            let prev = data
                .waiting_cnt
                .fetch_sub(WAITING_BIAS, Ordering::AcqRel);

            if data.mask9_waiting != 0 {
                if prev == WAITING_BIAS {
                    // All registered deps already notified during the scan;
                    // re-queue ourselves to re-scan with their now-`Ready`
                    // status.
                    self.queue.push(BiTask {
                        entry_idx: parent_entry_idx,
                        size_log2,
                    });
                }
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
            data.waiting_cnt
                .fetch_add(WAITING_BIAS, Ordering::Relaxed);
            for i in 0..4 {
                if data.mask4_waiting & (1 << i) == 0 {
                    continue;
                }
                let child_key = (data.arr0[i], data.arr1[i]);
                let child_idx = self.bicache_ref.entry(child_key);

                match handle_bi_dependency(&engine.bicache, child_idx, parent_entry_idx, size_log2)
                {
                    BiDependencyResult::Ready => {
                        data.mask4_waiting &= !(1 << i);
                        let val = self.bicache_ref.get(child_idx).payload.get_value();
                        data.arr0[i] = val.0;
                        data.arr1[i] = val.1;
                    }
                    BiDependencyResult::StartedByThisThread => {
                        data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                        self.queue.push(BiTask {
                            entry_idx: child_idx,
                            size_log2: size_log2 - 1,
                        });
                    }
                    BiDependencyResult::StartedByOtherThread => {
                        data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    }
                }
            }
            let prev = data
                .waiting_cnt
                .fetch_sub(WAITING_BIAS, Ordering::AcqRel);

            if data.mask4_waiting != 0 {
                if prev == WAITING_BIAS {
                    self.queue.push(BiTask {
                        entry_idx: parent_entry_idx,
                        size_log2,
                    });
                }
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

    /// Notify dependent entries that this dependency has completed.
    ///
    /// Atomically decrements each dependent's `waiting_cnt`. The thread that
    /// drives the counter to zero (this notifier or the owner's own
    /// `fetch_sub(WAITING_BIAS)`) re-queues the parent task. No lock is taken
    /// on the dependent entry: `BiProcessingData` is alive until `FINISHED`,
    /// which only its owner can publish, after `waiting_cnt == 0`.
    fn notify_dependents(&self, dependents: SmallVec<[BiTask; 2]>) {
        for dep in dependents {
            let entry = self.bicache_ref.get(dep.entry_idx);
            let dep_data: &BiProcessingData = entry.payload.get_ref();
            let prev = dep_data.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
            if prev == 1 {
                self.queue.push(BiTask {
                    entry_idx: dep.entry_idx,
                    size_log2: dep.size_log2,
                });
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
    let pd = BiProcessingData {
        dependents,
        ..Default::default()
    };
    entry.payload.set_ptr(Box::into_raw(Box::new(pd)));
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
            let child_data: &mut BiProcessingData = child_entry.payload.get_ref();
            child_data.dependents.push(BiTask {
                entry_idx: parent_entry_idx,
                size_log2: parent_size_log2,
            });
            status.fetch_and(!status::DEPS_LOCK, Ordering::Release);
            record_metric(spinner.count(), MetricKind::HandleBiDep);
            return BiDependencyResult::StartedByOtherThread;
        }
    }
}
