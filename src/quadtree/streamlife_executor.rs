//! # Parallel StreamLife Executor
//!
//! Work-stealing parallel executor for the StreamLife algorithm's
//! `update_binode` operation, with cross-engine async cooperation: HashLife
//! sub-results required by `update_binode`'s solitonic / base fast-paths are
//! computed asynchronously rather than via the synchronous `update_node_sync`
//! path. See `streamlife_async_design.md` for the full design.
//!
//! ## Two queues per worker
//!
//! Each worker holds two crossbeam deques:
//! - `bi_queue: Worker<BiTask>` — binode tasks (the existing work item).
//! - `hash_queue: Worker<Task>` — HashLife tasks descended from binode
//!   Phases Solitonic / Base.
//!
//! Pop policy: local LIFO bi first (keep recursion stack-warm), then local
//! LIFO hash, then steal — bi first, then hash, from a random victim.
//! HashLife's pure-engine path is unchanged: it still uses a single
//! `Worker<Task>`.
//!
//! ## Cross-engine dependents
//!
//! A binode task in Phase Solitonic or Base waits on the result of one or
//! two HashLife nodes. It registers itself on the HashLife node's
//! dependents list as `Dependent::Binode { entry_idx, size_log2 }`. HashLife
//! sub-children registered during async descent of a HashLife node use
//! `Dependent::Node { idx, size_log2 }`. The HashLife `notify_dependents`
//! dispatches by variant, pushing to `bi_queue` or `hash_queue`
//! appropriately.
//!
//! Dependents-list and `waiting_cnt` synchronization mirror the HashLife
//! executor — see [`super::hashlife_executor`] module docs for the full state
//! machine. The bit-flag state machine on `n.status` is shared across both
//! engines.

use super::{
    LEAF_SIZE_LOG2, algorithm,
    hashlife_executor::{
        DependencyHandlingResult, ProcessingData, ProcessingGuard, Task, handle_dependency,
        is_finished, update_node_async,
    },
    hashtable::{BinodeCache, BinodeCacheRef, Idx, NodeStoreRef},
    node::QuadTreeNode,
    sharded_statistics::*,
    spin::Spinner,
    status,
    streamlife::StreamLifeEngine,
};
use crossbeam::deque::{Steal, Stealer, Worker};
use smallvec::{SmallVec, smallvec};
use std::{
    mem,
    sync::atomic::{AtomicU8, AtomicU16, Ordering},
    thread,
    time::Duration,
};

/// Bias added to `waiting_cnt` while the owner is scanning children. See
/// [`super::hashlife_executor`] for the full rationale.
const WAITING_BIAS: u16 = 1 << 15;

/// A unit of work representing a binode pair to be processed.
#[derive(Clone, Copy)]
pub(super) struct BiTask {
    /// Index into the BinodeCache for this binode pair.
    pub(super) entry_idx: Idx,
    /// Size (log2) of the nodes in this pair.
    pub(super) size_log2: u32,
}

/// Tagged dependent for a HashLife `QuadTreeNode` processed during a
/// StreamLife run. A HashLife node's dependents list (under `Dep =
/// Dependent`) can hold either kind of waiter:
/// - `Node`: another HashLife node (descended from a binode task) is waiting.
/// - `Binode`: a binode task is waiting (Phases Solitonic / Base).
///
/// The `size_log2` is stored on the variant because the dependent's level is
/// not always derivable from the dependency's: a binode in Phase S/B depends
/// on a HashLife node at the *same* level, while a HashLife child is at one
/// level below its parent.
#[derive(Clone, Copy)]
pub(super) enum Dependent {
    Node { idx: Idx, size_log2: u32 },
    Binode { entry_idx: Idx, size_log2: u32 },
}

/// Phase tag for a `BiTask`'s state machine. Set on the first invocation
/// (Phase Entry) and read on every subsequent invocation to dispatch.
///
/// See `streamlife_async_design.md §3` for the full state machine.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
enum BiPhase {
    /// First invocation; phase not yet decided.
    #[default]
    Entry,
    /// Waiting for `node2lanes(idx.0)` and `node2lanes(idx.1)` so we can
    /// evaluate `is_solitonic` and dispatch to Solitonic/Base/Recursive.
    LaneWaitDecide,
    /// Two universes are provably non-interacting. Need async
    /// `update_node`-equivalent results for both `idx.0` and `idx.1`.
    Solitonic,
    /// In Solitonic finalization: one of `idx.0`, `idx.1` was blank, so we
    /// need lanes for the surviving universe `ind3` to pick the result tuple.
    LaneWaitSolitonic,
    /// Smallest recursive level. Universes merged synchronously; need async
    /// `update_node`-equivalent result for the merged node.
    Base,
    /// In Base finalization: `i3 != blank`, need lanes for the merged node to
    /// pick the result tuple.
    LaneWaitBase,
    /// Standard recursive case: 9-then-4 binode children. State tracked via
    /// existing `mask9_waiting` / `mask4_waiting` masks (no cross-engine
    /// dependents involved).
    Recursive,
}

/// A unit of work representing a node whose lane descriptor must be computed.
#[derive(Clone, Copy)]
pub(super) struct LaneTask {
    pub(super) idx: Idx,
    pub(super) size_log2: u32,
}

/// Tagged dependent for a `LaneTask`'s `LaneProcessingData`. A lane can have
/// either lane-task or binode-task waiters: lane tasks recurse into their
/// 9 children and wait for those children's lanes; binode tasks (Phase
/// LaneWaitDecide / LaneWaitSolitonic / LaneWaitBase) wait on lanes for
/// the is_solitonic decision or the finalization step.
#[derive(Clone, Copy)]
enum LaneDependent {
    Lane { idx: Idx, size_log2: u32 },
    Binode { entry_idx: Idx, size_log2: u32 },
}

/// Temporary data allocated during lane processing.
///
/// Heap-allocated when lane processing starts (transition NOT_STARTED →
/// PROCESSING on `n.status_extra`), freed when status_extra reaches FINISHED.
/// Stored via raw pointer in `n.extra` (which is `UnsafeCell<u64>` and big
/// enough for a pointer; it doubles as the storage for the final lane value
/// after FINISHED, mirroring how `n.cache` is dual-purposed for HashLife).
struct LaneProcessingData {
    /// Children Idxs; corners at indices 0,2,6,8; middles at 1,3,4,5,7.
    /// Corner Idxs are filled on first entry from the parent's parts;
    /// middle Idxs are computed and stored after the corner stage completes.
    children: [Idx; 9],
    /// Per-child lane results. Index aligned with `children`. A blank child's
    /// lane is pre-filled as 0xffff and the corresponding pending bit is
    /// cleared without dispatching a task.
    child_lanes: [u64; 9],
    /// Bits 0..=8 mark children whose lane is still in flight. After the
    /// corner stage, bits for unsatisfied corners stay set; once all corners
    /// are in, the parent task computes adml and either short-circuits (no
    /// middles) or repopulates `pending_mask` with the middle bits (1,3,4,5,7).
    pending_mask: u16,
    /// `true` after the corner stage completed and middle children were
    /// dispatched. Distinguishes the transient "init / corners" state from
    /// the post-corner "middles" state when `pending_mask == 0` between
    /// stages.
    middles_dispatched: bool,
    /// Count of dependencies still being computed; biased on each scan.
    waiting_cnt: AtomicU16,
    /// Tasks waiting on this lane's result. Drained at the finish barrier.
    dependents: SmallVec<[LaneDependent; 2]>,
}

impl Default for LaneProcessingData {
    fn default() -> Self {
        Self {
            children: [Idx::default(); 9],
            child_lanes: [0u64; 9],
            pending_mask: 0,
            middles_dispatched: false,
            waiting_cnt: AtomicU16::new(0),
            dependents: SmallVec::new(),
        }
    }
}

/// Indices of the 4 corner children in the 3×3 layout.
const LANE_CORNER_IDX: [usize; 4] = [0, 2, 6, 8];
/// Indices of the 5 middle children in the 3×3 layout.
const LANE_MIDDLE_IDX: [usize; 5] = [1, 3, 4, 5, 7];
/// `pending_mask` bits for corner children.
const LANE_CORNER_MASK: u16 = (1 << 0) | (1 << 2) | (1 << 6) | (1 << 8);
/// `pending_mask` bits for middle children.
const LANE_MIDDLE_MASK: u16 = (1 << 1) | (1 << 3) | (1 << 4) | (1 << 5) | (1 << 7);

/// Temporary data allocated during binode processing.
///
/// Heap-allocated when processing starts, freed when entry reaches FINISHED state.
/// Stored via pointer in the cache entry's payload field.
struct BiProcessingData {
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
    ///   Phase Solitonic: hash_results[0] = i1 (for idx.0), hash_results[1] = i2 (for idx.1).
    ///   Phase Base: hash_results[0] = i3 (for the merged node stored in arr0[0]).
    hash_results: [Idx; 2],
    /// Bitmask of pending HashLife results for Phases Solitonic / Base.
    /// Solitonic uses bits 0,1; Base uses bit 0 only.
    hash_mask: u8,
    /// Lane-target Idxs whose lane descriptor we are awaiting.
    ///   Phase LaneWaitDecide: lane_targets[0] = idx.0, lane_targets[1] = idx.1.
    ///   Phase LaneWaitSolitonic: lane_targets[0] = ind3 (the non-blank survivor).
    ///   Phase LaneWaitBase: lane_targets[0] = merged.
    lane_targets: [Idx; 2],
    /// Lane descriptors received from completed `LaneTask`s.
    lane_results: [u64; 2],
    /// Bitmask of pending lane requests. LaneWaitDecide uses bits 0,1;
    /// LaneWaitSolitonic / LaneWaitBase use bit 0 only.
    lane_mask: u8,
    /// Count of dependencies still being computed. The entry resumes when
    /// this reaches 0. Manipulated lock-free with the bias trick.
    waiting_cnt: AtomicU16,
    /// Entries that registered as dependents of this entry. Mutated by the
    /// owner exclusively during the init / finish barriers, and by pushers
    /// in parallel under [`status::DEPS_LOCK`].
    dependents: SmallVec<[BiTask; 2]>,
}

impl Default for BiProcessingData {
    fn default() -> Self {
        Self {
            phase: BiPhase::default(),
            arr0: [Idx::default(); 9],
            arr1: [Idx::default(); 9],
            mask9_waiting: 0,
            mask4_waiting: 0,
            hash_results: [Idx::default(); 2],
            hash_mask: 0,
            lane_targets: [Idx::default(); 2],
            lane_results: [0u64; 2],
            lane_mask: 0,
            waiting_cnt: AtomicU16::new(0),
            dependents: SmallVec::new(),
        }
    }
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

        // Create worker queues and stealers for all three task kinds.
        let mut bi_queues = Vec::with_capacity(num_threads);
        let mut bi_stealers = Vec::with_capacity(num_threads);
        let mut hash_queues = Vec::with_capacity(num_threads);
        let mut hash_stealers = Vec::with_capacity(num_threads);
        let mut lane_queues = Vec::with_capacity(num_threads);
        let mut lane_stealers = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let bi_queue = Worker::new_lifo();
            let hash_queue = Worker::new_lifo();
            let lane_queue = Worker::new_lifo();
            bi_stealers.push(bi_queue.stealer());
            hash_stealers.push(hash_queue.stealer());
            lane_stealers.push(lane_queue.stealer());
            bi_queues.push(bi_queue);
            hash_queues.push(hash_queue);
            lane_queues.push(lane_queue);
        }

        // Claim root entry and push initial task
        start_processing_entry(bicache, root_idx, smallvec![]);
        bi_queues[0].push(BiTask {
            entry_idx: root_idx,
            size_log2: self.size_log2,
        });

        let mut total_stats = ExecutionStatistics::new();
        thread::scope(|scope| {
            let mut handles = Vec::with_capacity(num_threads);
            for (thread_idx, ((bi_queue, hash_queue), lane_queue)) in bi_queues
                .into_iter()
                .zip(hash_queues.into_iter())
                .zip(lane_queues.into_iter())
                .enumerate()
            {
                let executor_thread = BiExecutorThread {
                    engine: self.engine,
                    bicache_ref: bicache.create_ref(thread_idx),
                    node_ref: self.engine.base.mem.create_ref(thread_idx),
                    root_status,
                    thread_idx,
                    bi_queue,
                    hash_queue,
                    lane_queue,
                    bi_stealers: &bi_stealers,
                    hash_stealers: &hash_stealers,
                    lane_stealers: &lane_stealers,
                };
                handles.push(scope.spawn(move || executor_thread.run()));
            }

            for handle in handles {
                total_stats.merge_from(&handle.join().unwrap());
            }
        });

        if self.engine.base.mem.exceeds_load_factor() || bicache.exceeds_load_factor() {
            self.free_orphaned_processing_data();
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

    /// Drop orphaned `ProcessingData<Dependent>` (HashLife nodes),
    /// `BiProcessingData` (binode entries), and `LaneProcessingData` (HashLife
    /// nodes whose lanes were being computed) on cancellation. Must be called
    /// from a single-threaded context after `thread::scope` has joined; only
    /// PENDING slots own a live box at that point.
    fn free_orphaned_processing_data(&self) {
        // Binode entries
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
        // HashLife nodes processed asynchronously during this StreamLife run
        // can also be orphaned in PENDING state. Free their
        // `ProcessingData<Dependent>` boxes (cache field) and any orphan
        // `LaneProcessingData` (extra field, status_extra machine).
        let mem = &self.engine.base.mem;
        for idx in 0..mem.capacity() {
            let n = mem.get(idx as Idx);
            let status = n.status.load(Ordering::Relaxed);
            if status == status::PENDING {
                let pd: &mut ProcessingData<Dependent> = n.cache.get_ref();
                // SAFETY: produced by `Box::into_raw` in
                // `start_processing_node`; all workers have joined.
                unsafe { drop(Box::from_raw(pd as *mut ProcessingData<Dependent>)) };
            }
            let status_extra = n.status_extra.load(Ordering::Relaxed);
            if status_extra == status::PENDING {
                let pd = lane_pd_ref(n);
                // SAFETY: produced by `Box::into_raw` in
                // `start_processing_lane`; all workers have joined.
                unsafe { drop(Box::from_raw(pd as *mut LaneProcessingData)) };
            }
        }
    }
}

/// Per-thread worker for the StreamLife parallel executor.
///
/// Holds three deques (binode, lane, HashLife) and processes work from any
/// kind, with a custom three-queue fetch loop in [`Self::run`].
struct BiExecutorThread<'a> {
    engine: &'a StreamLifeEngine,
    bicache_ref: BinodeCacheRef<'a>,
    node_ref: NodeStoreRef<'a, u64>,
    root_status: &'a AtomicU8,
    thread_idx: usize,
    bi_queue: Worker<BiTask>,
    hash_queue: Worker<Task>,
    lane_queue: Worker<LaneTask>,
    bi_stealers: &'a [Stealer<BiTask>],
    hash_stealers: &'a [Stealer<Task>],
    lane_stealers: &'a [Stealer<LaneTask>],
}

impl<'a> BiExecutorThread<'a> {
    /// Initial backoff for the steal-then-sleep loop.
    const INITIAL_WAIT: Duration = Duration::from_micros(100);
    /// Maximum backoff.
    const MAX_WAIT: Duration = Duration::from_millis(100);
    /// Number of random victims to attempt per outer iteration before sleeping.
    const STEAL_ATTEMPTS: usize = 2;

    fn run(&self) -> ExecutionStatistics {
        set_current_execution_stats();

        let mut rng = <rand_chacha::ChaCha8Rng as rand::SeedableRng>::from_os_rng();
        let mut wait_duration = Self::INITIAL_WAIT;
        let mut last_bi_victim = 0usize;
        let mut last_lane_victim = 0usize;
        let mut last_hash_victim = 0usize;

        'outer: loop {
            // Cancellation: load factor exceeded on either store.
            if self.engine.base.mem.exceeds_load_factor()
                || self.bicache_ref.exceeds_load_factor()
            {
                break;
            }

            // Local LIFO: prefer binode work to keep the recursion stack warm,
            // then lanes (which directly unblock binodes), then HashLife.
            if let Some(task) = self.bi_queue.pop() {
                self.timed_process_bi_task(task);
                wait_duration = Self::INITIAL_WAIT;
                continue;
            }
            if let Some(task) = self.lane_queue.pop() {
                self.timed_process_lane_task(task);
                wait_duration = Self::INITIAL_WAIT;
                continue;
            }
            if let Some(task) = self.hash_queue.pop() {
                self.timed_process_hash_task(task);
                wait_duration = Self::INITIAL_WAIT;
                continue;
            }

            // Termination condition checked after local pops fail (so we
            // drain any remaining local work).
            if is_finished(self.root_status) {
                break;
            }

            let n = self.bi_stealers.len();
            if n > 1 {
                // Try last successful victim first (locality / hot cache).
                let bi_lv = self.try_steal_bi(last_bi_victim);
                record_last_victim_steal(&bi_lv);
                if let Some(task) = bi_lv {
                    self.timed_process_bi_task(task);
                    wait_duration = Self::INITIAL_WAIT;
                    continue;
                }
                let lane_lv = self.try_steal_lane(last_lane_victim);
                record_last_victim_steal(&lane_lv);
                if let Some(task) = lane_lv {
                    self.timed_process_lane_task(task);
                    wait_duration = Self::INITIAL_WAIT;
                    continue;
                }
                let hash_lv = self.try_steal_hash(last_hash_victim);
                record_last_victim_steal(&hash_lv);
                if let Some(task) = hash_lv {
                    self.timed_process_hash_task(task);
                    wait_duration = Self::INITIAL_WAIT;
                    continue;
                }

                // Random victim selection. Order: bi > lane > hash. Lanes are
                // pulled before hash because a finished lane unblocks a binode
                // directly; HashLife tasks are an auxiliary path.
                for _ in 0..Self::STEAL_ATTEMPTS {
                    let victim = self.random_victim(&mut rng, n);
                    if self.bi_stealers[victim].len() > 0
                        && let Some(task) = self.try_steal_bi(victim)
                    {
                        last_bi_victim = victim;
                        self.timed_process_bi_task(task);
                        wait_duration = Self::INITIAL_WAIT;
                        continue 'outer;
                    }
                    if self.lane_stealers[victim].len() > 0
                        && let Some(task) = self.try_steal_lane(victim)
                    {
                        last_lane_victim = victim;
                        self.timed_process_lane_task(task);
                        wait_duration = Self::INITIAL_WAIT;
                        continue 'outer;
                    }
                    if self.hash_stealers[victim].len() > 0
                        && let Some(task) = self.try_steal_hash(victim)
                    {
                        last_hash_victim = victim;
                        self.timed_process_hash_task(task);
                        wait_duration = Self::INITIAL_WAIT;
                        continue 'outer;
                    }
                }
            }

            thread::sleep(wait_duration);
            wait_duration = Self::MAX_WAIT.min(wait_duration * 2);
        }

        take_current_execution_stats().unwrap()
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

    fn timed_process_lane_task(&self, task: LaneTask) {
        let start = Ticks::now();
        self.process_lane_task(task);
        record_task_duration(Ticks::now().elapsed_since(start));
    }

    fn random_victim(&self, rng: &mut rand_chacha::ChaCha8Rng, n: usize) -> usize {
        use rand::Rng;
        // Don't steal from yourself.
        let mut i = rng.random_range(0..n - 1);
        if i >= self.thread_idx {
            i += 1;
        }
        i
    }

    fn try_steal_bi(&self, victim: usize) -> Option<BiTask> {
        loop {
            let result = self.bi_stealers[victim]
                .steal_batch_with_limit_and_pop(&self.bi_queue, 1);
            record_steal(&result);
            match result {
                Steal::Success(task) => return Some(task),
                Steal::Empty => return None,
                Steal::Retry => continue,
            }
        }
    }

    fn try_steal_hash(&self, victim: usize) -> Option<Task> {
        loop {
            let result = self.hash_stealers[victim]
                .steal_batch_with_limit_and_pop(&self.hash_queue, 1);
            record_steal(&result);
            match result {
                Steal::Success(task) => return Some(task),
                Steal::Empty => return None,
                Steal::Retry => continue,
            }
        }
    }

    fn try_steal_lane(&self, victim: usize) -> Option<LaneTask> {
        loop {
            let result = self.lane_stealers[victim]
                .steal_batch_with_limit_and_pop(&self.lane_queue, 1);
            record_steal(&result);
            match result {
                Steal::Success(task) => return Some(task),
                Steal::Empty => return None,
                Steal::Retry => continue,
            }
        }
    }

    /// Process a single binode task: drive its phase machine.
    fn process_bi_task(&self, task: BiTask) {
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
            self.notify_bi_dependents(dependents);
        }
    }

    /// Process a single lane task: drive its `LaneProcessingData` state
    /// machine on `n.status_extra` (corners stage → middles stage → combine).
    fn process_lane_task(&self, task: LaneTask) {
        let n = self.node_ref.get(task.idx);
        let mut guard = ProcessingGuard::new(&n.status_extra, MetricKind::ProcessTask);
        let data = lane_pd_ref(n);
        if let Some(result) = self.update_lane(&task, data) {
            guard.enter_finish_barrier(MetricKind::NotifyDep);
            let mut dependents: SmallVec<[LaneDependent; 2]> = SmallVec::new();
            mem::swap(&mut data.dependents, &mut dependents);
            // Overwrite the pointer with the final lane value before publishing
            // FINISHED, just like the cache field for HashLife/binodes.
            unsafe { *n.extra.get() = result };
            guard.publish_finished();
            unsafe { drop(Box::from_raw(data as *mut LaneProcessingData)) };
            self.notify_lane_dependents(dependents);
        }
    }

    /// Compute lane result or yield, advancing the corner/middle stage
    /// machine on the `LaneProcessingData`. Returns `Some(result)` when
    /// ready, `None` when waiting on at least one child lane.
    fn update_lane(&self, task: &LaneTask, data: &mut LaneProcessingData) -> Option<u64> {
        let n = self.node_ref.get(task.idx);
        let blank_nodes = &self.engine.base.blank_nodes;
        let dep = LaneDependent::Lane {
            idx: task.idx,
            size_log2: task.size_log2,
        };

        // First entry: handle the LL+1 base case directly, or set up the
        // corner stage by reading parts and pre-filling blanks.
        if data.pending_mask == 0 && !data.middles_dispatched {
            if task.size_log2 == LEAF_SIZE_LOG2 + 1 {
                return Some(algorithm::lane_base_case(
                    &self.node_ref,
                    n.nw,
                    n.ne,
                    n.sw,
                    n.se,
                ));
            }
            data.children[0] = n.nw;
            data.children[2] = n.ne;
            data.children[6] = n.sw;
            data.children[8] = n.se;
            data.pending_mask = LANE_CORNER_MASK;
            let blank_child = blank_nodes.get(task.size_log2 - 1);
            for &i in &LANE_CORNER_IDX {
                if data.children[i] == blank_child {
                    data.child_lanes[i] = 0xffff;
                    data.pending_mask &= !(1 << i);
                }
            }
        }

        // Stage Corners — dispatch / wait until all 4 corner lanes are in.
        if !data.middles_dispatched {
            if data.pending_mask != 0 {
                data.waiting_cnt
                    .fetch_add(WAITING_BIAS, Ordering::Relaxed);
                for &i in &LANE_CORNER_IDX {
                    if data.pending_mask & (1 << i) == 0 {
                        continue;
                    }
                    let child = data.children[i];
                    let child_node = self.node_ref.get(child);
                    match handle_lane_dependency(child_node, dep) {
                        LaneDependencyResult::Ready => {
                            data.pending_mask &= !(1 << i);
                            data.child_lanes[i] = unsafe { *child_node.extra.get() };
                        }
                        LaneDependencyResult::StartedByThisThread => {
                            data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                            self.lane_queue.push(LaneTask {
                                idx: child,
                                size_log2: task.size_log2 - 1,
                            });
                        }
                        LaneDependencyResult::StartedByOtherThread => {
                            data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                }
                let prev = data
                    .waiting_cnt
                    .fetch_sub(WAITING_BIAS, Ordering::AcqRel);
                if data.pending_mask != 0 {
                    if prev == WAITING_BIAS {
                        self.lane_queue.push(LaneTask {
                            idx: task.idx,
                            size_log2: task.size_log2,
                        });
                    }
                    return None;
                }
            }

            // All corners ready. Short-circuit if their AND zeroes adml.
            let corner_adml = data.child_lanes[0]
                & data.child_lanes[2]
                & data.child_lanes[6]
                & data.child_lanes[8]
                & 0xff;
            if corner_adml == 0 {
                return Some(0);
            }

            // Prepare middle children and set up the next stage.
            let middles = algorithm::lane_middle_children(
                &self.node_ref,
                n.nw,
                n.ne,
                n.sw,
                n.se,
                task.size_log2,
            );
            for (slot_pos, &m) in LANE_MIDDLE_IDX.iter().zip(middles.iter()) {
                data.children[*slot_pos] = m;
            }
            data.pending_mask = LANE_MIDDLE_MASK;
            let blank_child = blank_nodes.get(task.size_log2 - 1);
            for &i in &LANE_MIDDLE_IDX {
                if data.children[i] == blank_child {
                    data.child_lanes[i] = 0xffff;
                    data.pending_mask &= !(1 << i);
                }
            }
            data.middles_dispatched = true;
        }

        // Stage Middles — dispatch / wait until all 5 middle lanes are in.
        if data.pending_mask != 0 {
            data.waiting_cnt
                .fetch_add(WAITING_BIAS, Ordering::Relaxed);
            for &i in &LANE_MIDDLE_IDX {
                if data.pending_mask & (1 << i) == 0 {
                    continue;
                }
                let child = data.children[i];
                let child_node = self.node_ref.get(child);
                match handle_lane_dependency(child_node, dep) {
                    LaneDependencyResult::Ready => {
                        data.pending_mask &= !(1 << i);
                        data.child_lanes[i] = unsafe { *child_node.extra.get() };
                    }
                    LaneDependencyResult::StartedByThisThread => {
                        data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                        self.lane_queue.push(LaneTask {
                            idx: child,
                            size_log2: task.size_log2 - 1,
                        });
                    }
                    LaneDependencyResult::StartedByOtherThread => {
                        data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    }
                }
            }
            let prev = data
                .waiting_cnt
                .fetch_sub(WAITING_BIAS, Ordering::AcqRel);
            if data.pending_mask != 0 {
                if prev == WAITING_BIAS {
                    self.lane_queue.push(LaneTask {
                        idx: task.idx,
                        size_log2: task.size_log2,
                    });
                }
                return None;
            }
        }

        // All 9 lanes ready: combine.
        Some(algorithm::lane_combine(&data.child_lanes, task.size_log2))
    }

    /// Notify dependents of a finished lane, dispatching by variant.
    fn notify_lane_dependents(&self, dependents: SmallVec<[LaneDependent; 2]>) {
        for dep in dependents {
            match dep {
                LaneDependent::Lane { idx, size_log2 } => {
                    let n = self.node_ref.get(idx);
                    let pd = lane_pd_ref(n);
                    let prev = pd.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
                    if prev == 1 {
                        self.lane_queue.push(LaneTask { idx, size_log2 });
                    }
                }
                LaneDependent::Binode {
                    entry_idx,
                    size_log2,
                } => {
                    let entry = self.bicache_ref.get(entry_idx);
                    let pd: &BiProcessingData = entry.payload.get_ref();
                    let prev = pd.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
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

    /// Process a single HashLife task descended from a binode Phase S/B.
    /// Mirror of HashLife's `process_task` but uses
    /// `ProcessingData<Dependent>` so cross-engine waiters can register.
    fn process_hash_task(&self, task: Task) {
        let n = self.node_ref.get(task.idx);
        let mut guard = ProcessingGuard::new(&n.status, MetricKind::ProcessTask);
        let data: &mut ProcessingData<Dependent> = n.cache.get_ref();
        let dep = Dependent::Node {
            idx: task.idx,
            size_log2: task.size_log2,
        };
        let parts = n.parts();
        let result = update_node_async(
            &self.node_ref,
            &self.hash_queue,
            self.engine.base.generations_per_update_log2.unwrap(),
            &task,
            parts,
            data,
            dep,
        );
        if let Some(result) = result {
            guard.enter_finish_barrier(MetricKind::NotifyDep);
            let mut dependents: SmallVec<[Dependent; 2]> = SmallVec::new();
            mem::swap(&mut data.dependents, &mut dependents);
            n.cache.set_value(result);
            guard.publish_finished();
            unsafe { drop(Box::from_raw(data as *mut ProcessingData<Dependent>)) };
            self.notify_node_dependents(dependents);
        }
    }

    /// Compute binode result or yield, advancing the phase machine.
    ///
    /// On the first invocation, sets up the lane-wait phase that will
    /// asynchronously fetch the lane descriptors needed for the
    /// `is_solitonic` decision. On subsequent invocations, reads the stored
    /// phase and dispatches.
    ///
    /// Returns `Some(result)` when the task can be finalized, `None` when
    /// at least one dependency is still in flight (wake-up duty transferred
    /// via the `waiting_cnt` bias trick).
    fn update_binode(
        &self,
        parent_entry_idx: Idx,
        idx: (Idx, Idx),
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let engine = self.engine;

        // === Phase Entry: first invocation, set up lane wait for the
        // is_solitonic decision and fall through to LaneWaitDecide.
        //
        // Invariant: every call into algorithm:: from this executor must go
        // through `self.node_ref` (a per-thread `NodeStoreRef`) so that
        // allocations land in this thread's chunk pool and free list. Calling
        // `engine.base.mem.find_or_create_*` directly funnels every worker
        // through shard 0 of the underlying `ConcurrentHashTable`, which races
        // on the bump pointer / free list and produces torn slot bodies.
        if data.phase == BiPhase::Entry {
            data.phase = BiPhase::LaneWaitDecide;
            let blank = engine.base.blank_nodes.get(size_log2);
            data.lane_targets = [idx.0, idx.1];
            data.lane_mask = 0;
            for b in 0..2 {
                if data.lane_targets[b] == blank {
                    // Blank universes have lane = 0xffff by convention; no
                    // dispatch needed.
                    data.lane_results[b] = 0xffff;
                } else {
                    data.lane_mask |= 1 << b;
                }
            }
        }

        // Dispatch by phase.
        match data.phase {
            BiPhase::Entry => unreachable!("Entry should have been transitioned"),
            BiPhase::LaneWaitDecide => {
                self.lane_wait_decide_phase(parent_entry_idx, idx, size_log2, data)
            }
            BiPhase::Solitonic => self.solitonic_phase(parent_entry_idx, idx, size_log2, data),
            BiPhase::LaneWaitSolitonic => {
                self.lane_wait_solitonic_phase(parent_entry_idx, idx, size_log2, data)
            }
            BiPhase::Base => self.base_phase(parent_entry_idx, size_log2, data),
            BiPhase::LaneWaitBase => self.lane_wait_base_phase(parent_entry_idx, size_log2, data),
            BiPhase::Recursive => self.recursive_phase(parent_entry_idx, size_log2, data),
        }
    }

    /// Phase LaneWaitDecide: await `node2lanes(idx.0)` and `node2lanes(idx.1)`,
    /// then evaluate `is_solitonic` and tail-call into the resulting phase.
    fn lane_wait_decide_phase(
        &self,
        parent_entry_idx: Idx,
        idx: (Idx, Idx),
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let engine = self.engine;
        let gens_log2 = engine.base.generations_per_update_log2.unwrap();

        if data.lane_mask != 0 {
            let dep = LaneDependent::Binode {
                entry_idx: parent_entry_idx,
                size_log2,
            };
            data.waiting_cnt
                .fetch_add(WAITING_BIAS, Ordering::Relaxed);
            for b in 0..2 {
                if data.lane_mask & (1 << b) == 0 {
                    continue;
                }
                let target = data.lane_targets[b];
                let target_node = self.node_ref.get(target);
                match handle_lane_dependency(target_node, dep) {
                    LaneDependencyResult::Ready => {
                        data.lane_mask &= !(1 << b);
                        data.lane_results[b] = unsafe { *target_node.extra.get() };
                    }
                    LaneDependencyResult::StartedByThisThread => {
                        data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                        self.lane_queue.push(LaneTask {
                            idx: target,
                            size_log2,
                        });
                    }
                    LaneDependencyResult::StartedByOtherThread => {
                        data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    }
                }
            }
            let prev = data
                .waiting_cnt
                .fetch_sub(WAITING_BIAS, Ordering::AcqRel);
            if data.lane_mask != 0 {
                if prev == WAITING_BIAS {
                    self.bi_queue.push(BiTask {
                        entry_idx: parent_entry_idx,
                        size_log2,
                    });
                }
                return None;
            }
        }

        // Both lanes available. Decide which phase to enter and set up its
        // scratch fields, then tail-call.
        let lanes1 = data.lane_results[0];
        let lanes2 = data.lane_results[1];
        if algorithm::is_solitonic_from_lanes(lanes1, lanes2) {
            data.phase = BiPhase::Solitonic;
            data.hash_mask = 0b11;
        } else if size_log2 == LEAF_SIZE_LOG2 + 2 {
            data.phase = BiPhase::Base;
            let merged = algorithm::merge_universes(
                &self.node_ref,
                &engine.base.blank_nodes,
                idx,
                size_log2,
            );
            data.arr0[0] = merged;
            data.hash_mask = 0b1;
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
            }
        }

        match data.phase {
            BiPhase::Solitonic => self.solitonic_phase(parent_entry_idx, idx, size_log2, data),
            BiPhase::Base => self.base_phase(parent_entry_idx, size_log2, data),
            BiPhase::Recursive => self.recursive_phase(parent_entry_idx, size_log2, data),
            _ => unreachable!(),
        }
    }

    /// Phase Solitonic: wait for `update_node_async`-equivalent of
    /// `idx.0` and `idx.1`, then assemble.
    fn solitonic_phase(
        &self,
        parent_entry_idx: Idx,
        idx: (Idx, Idx),
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let engine = self.engine;
        let targets = [idx.0, idx.1];
        let dep = Dependent::Binode {
            entry_idx: parent_entry_idx,
            size_log2,
        };

        if data.hash_mask != 0 {
            data.waiting_cnt
                .fetch_add(WAITING_BIAS, Ordering::Relaxed);
            for b in 0..2 {
                if data.hash_mask & (1 << b) == 0 {
                    continue;
                }
                let target = targets[b];
                let target_node = self.node_ref.get(target);
                match handle_dependency(target_node, dep) {
                    DependencyHandlingResult::Ready => {
                        data.hash_mask &= !(1 << b);
                        data.hash_results[b] = target_node.cache.get_value();
                    }
                    DependencyHandlingResult::StartedByThisThread => {
                        data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                        self.hash_queue.push(Task::new(target, size_log2));
                    }
                    DependencyHandlingResult::StartedByOtherThread => {
                        data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    }
                }
            }
            let prev = data
                .waiting_cnt
                .fetch_sub(WAITING_BIAS, Ordering::AcqRel);
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

        // Both hash results in. Finalize per `compute_solitonic` semantics.
        let i1 = data.hash_results[0];
        let i2 = data.hash_results[1];
        let b = engine.base.blank_nodes.get(size_log2);
        if idx.0 == b || idx.1 == b {
            // Need lanes for the surviving universe to pick the result tuple.
            // Transition to LaneWaitSolitonic and tail-call.
            let ind3 = if idx.0 == b { idx.1 } else { idx.0 };
            data.phase = BiPhase::LaneWaitSolitonic;
            data.lane_targets[0] = ind3;
            data.lane_mask = if ind3 == b {
                // Defensive: both blank shouldn't be reachable here
                // (is_solitonic on a blank input bails to recursive), but if
                // it ever is, treat the lane as the blank constant.
                data.lane_results[0] = 0xffff;
                0
            } else {
                0b1
            };
            return self.lane_wait_solitonic_phase(parent_entry_idx, idx, size_log2, data);
        }
        Some((i1, i2))
    }

    /// Phase LaneWaitSolitonic: await `node2lanes(ind3)`, then build the
    /// final tuple from the lane bit and the surviving hash result.
    fn lane_wait_solitonic_phase(
        &self,
        parent_entry_idx: Idx,
        idx: (Idx, Idx),
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let engine = self.engine;
        if data.lane_mask != 0 {
            let dep = LaneDependent::Binode {
                entry_idx: parent_entry_idx,
                size_log2,
            };
            data.waiting_cnt
                .fetch_add(WAITING_BIAS, Ordering::Relaxed);
            let target = data.lane_targets[0];
            let target_node = self.node_ref.get(target);
            match handle_lane_dependency(target_node, dep) {
                LaneDependencyResult::Ready => {
                    data.lane_mask &= !0b1;
                    data.lane_results[0] = unsafe { *target_node.extra.get() };
                }
                LaneDependencyResult::StartedByThisThread => {
                    data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    self.lane_queue.push(LaneTask {
                        idx: target,
                        size_log2,
                    });
                }
                LaneDependencyResult::StartedByOtherThread => {
                    data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                }
            }
            let prev = data
                .waiting_cnt
                .fetch_sub(WAITING_BIAS, Ordering::AcqRel);
            if data.lane_mask != 0 {
                if prev == WAITING_BIAS {
                    self.bi_queue.push(BiTask {
                        entry_idx: parent_entry_idx,
                        size_log2,
                    });
                }
                return None;
            }
        }

        let lanes = data.lane_results[0];
        let b = engine.base.blank_nodes.get(size_log2);
        let i3 = if idx.0 == b {
            data.hash_results[1]
        } else {
            data.hash_results[0]
        };
        let blank_child = engine.base.blank_nodes.get(size_log2 - 1);
        let result = if lanes & 0xf0 != 0 {
            (blank_child, i3)
        } else {
            (i3, blank_child)
        };
        Some(result)
    }

    /// Phase Base: wait for `update_node_async`-equivalent of the merged
    /// universe, then assemble.
    fn base_phase(
        &self,
        parent_entry_idx: Idx,
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let engine = self.engine;
        let merged = data.arr0[0];
        let dep = Dependent::Binode {
            entry_idx: parent_entry_idx,
            size_log2,
        };

        if data.hash_mask != 0 {
            data.waiting_cnt
                .fetch_add(WAITING_BIAS, Ordering::Relaxed);
            // Only bit 0 is used for Phase Base.
            let target_node = self.node_ref.get(merged);
            match handle_dependency(target_node, dep) {
                DependencyHandlingResult::Ready => {
                    data.hash_mask &= !0b1;
                    data.hash_results[0] = target_node.cache.get_value();
                }
                DependencyHandlingResult::StartedByThisThread => {
                    data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    self.hash_queue.push(Task::new(merged, size_log2));
                }
                DependencyHandlingResult::StartedByOtherThread => {
                    data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                }
            }
            let prev = data
                .waiting_cnt
                .fetch_sub(WAITING_BIAS, Ordering::AcqRel);
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
        if i3 != blank_child {
            // Need lanes on the merged node. Transition to LaneWaitBase.
            data.phase = BiPhase::LaneWaitBase;
            data.lane_targets[0] = merged;
            data.lane_mask = 0b1;
            return self.lane_wait_base_phase(parent_entry_idx, size_log2, data);
        }
        Some((blank_child, blank_child))
    }

    /// Phase LaneWaitBase: await `node2lanes(merged)`, then build the final
    /// tuple from the lane bit and `i3`.
    fn lane_wait_base_phase(
        &self,
        parent_entry_idx: Idx,
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let engine = self.engine;
        if data.lane_mask != 0 {
            let dep = LaneDependent::Binode {
                entry_idx: parent_entry_idx,
                size_log2,
            };
            data.waiting_cnt
                .fetch_add(WAITING_BIAS, Ordering::Relaxed);
            let target = data.lane_targets[0];
            let target_node = self.node_ref.get(target);
            match handle_lane_dependency(target_node, dep) {
                LaneDependencyResult::Ready => {
                    data.lane_mask &= !0b1;
                    data.lane_results[0] = unsafe { *target_node.extra.get() };
                }
                LaneDependencyResult::StartedByThisThread => {
                    data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    self.lane_queue.push(LaneTask {
                        idx: target,
                        size_log2,
                    });
                }
                LaneDependencyResult::StartedByOtherThread => {
                    data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                }
            }
            let prev = data
                .waiting_cnt
                .fetch_sub(WAITING_BIAS, Ordering::AcqRel);
            if data.lane_mask != 0 {
                if prev == WAITING_BIAS {
                    self.bi_queue.push(BiTask {
                        entry_idx: parent_entry_idx,
                        size_log2,
                    });
                }
                return None;
            }
        }

        let lanes = data.lane_results[0];
        let i3 = data.hash_results[0];
        let blank_child = engine.base.blank_nodes.get(size_log2 - 1);
        let result = if lanes & 0xf0 != 0 {
            (blank_child, i3)
        } else {
            (i3, blank_child)
        };
        Some(result)
    }

    /// Phase Recursive: existing 9-then-4 binode children logic.
    fn recursive_phase(
        &self,
        parent_entry_idx: Idx,
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let engine = self.engine;

        // Stage 1: Wait for 9 overlapping children (if both_stages).
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
                        self.bi_queue.push(BiTask {
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
        data.waiting_cnt
            .fetch_add(WAITING_BIAS, Ordering::Relaxed);
        for i in 0..4 {
            if data.mask4_waiting & (1 << i) == 0 {
                continue;
            }
            let child_key = (data.arr0[i], data.arr1[i]);
            let child_idx = self.bicache_ref.entry(child_key);
            match handle_bi_dependency(&engine.bicache, child_idx, parent_entry_idx, size_log2) {
                BiDependencyResult::Ready => {
                    data.mask4_waiting &= !(1 << i);
                    let val = self.bicache_ref.get(child_idx).payload.get_value();
                    data.arr0[i] = val.0;
                    data.arr1[i] = val.1;
                }
                BiDependencyResult::StartedByThisThread => {
                    data.waiting_cnt.fetch_add(1, Ordering::Relaxed);
                    self.bi_queue.push(BiTask {
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
    /// that drives the counter to zero re-queues the parent BiTask.
    fn notify_bi_dependents(&self, dependents: SmallVec<[BiTask; 2]>) {
        for dep in dependents {
            let entry = self.bicache_ref.get(dep.entry_idx);
            let dep_data: &BiProcessingData = entry.payload.get_ref();
            let prev = dep_data.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
            if prev == 1 {
                self.bi_queue.push(BiTask {
                    entry_idx: dep.entry_idx,
                    size_log2: dep.size_log2,
                });
            }
        }
    }

    /// Notify dependents of a finished HashLife node, dispatching by
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
                    let pd: &ProcessingData<Dependent> = n.cache.get_ref();
                    let prev = pd.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
                    if prev == 1 {
                        self.hash_queue.push(Task::new(idx, size_log2));
                    }
                }
                Dependent::Binode {
                    entry_idx,
                    size_log2,
                } => {
                    let entry = self.bicache_ref.get(entry_idx);
                    let pd: &BiProcessingData = entry.payload.get_ref();
                    let prev = pd.waiting_cnt.fetch_sub(1, Ordering::AcqRel);
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

// ============================================================================
// Lane async machinery — full ProcessingData-style state machine on
// `n.status_extra`, mirroring the HashLife/Binode versions but storing the
// `Box<LaneProcessingData>` raw pointer in `n.extra` instead of a separate
// cache field.
// ============================================================================

/// SAFETY: the caller asserts `n.status_extra` is in a state (PENDING /
/// ACTIVE / DEPS_LOCK overlay) where `n.extra` holds a live
/// `Box<LaneProcessingData>` pointer installed by `start_processing_lane`.
fn lane_pd_ref(n: &QuadTreeNode<u64>) -> &mut LaneProcessingData {
    unsafe { &mut *(*n.extra.get() as *mut LaneProcessingData) }
}

/// Initialize `n.status_extra` for lane processing by transitioning
/// `NOT_STARTED → PROCESSING → PENDING`. Mirrors `start_processing_node` /
/// `start_processing_entry`.
fn start_processing_lane(
    n: &QuadTreeNode<u64>,
    dependents: SmallVec<[LaneDependent; 2]>,
) -> bool {
    if n
        .status_extra
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

    let pd = LaneProcessingData {
        dependents,
        ..Default::default()
    };
    unsafe { *n.extra.get() = Box::into_raw(Box::new(pd)) as u64 };
    n.status_extra
        .fetch_xor(status::PROCESSING | status::PENDING, Ordering::Release);
    record_status_claim_success();
    true
}

/// Result of attempting to handle a lane dependency.
enum LaneDependencyResult {
    /// Dependency already computed; result available in `n.extra` as `u64`.
    Ready,
    /// This thread successfully claimed the dependency for processing.
    StartedByThisThread,
    /// Another thread is processing it; we registered as dependent.
    StartedByOtherThread,
}

/// Handle a lane dependency: check if ready, claim for processing, or
/// register as dependent. Mirrors `handle_dependency` / `handle_bi_dependency`
/// but operates on `n.status_extra` and `n.extra`.
fn handle_lane_dependency(
    n: &QuadTreeNode<u64>,
    dep: LaneDependent,
) -> LaneDependencyResult {
    let mut spinner = Spinner::new();
    loop {
        let cur = n.status_extra.load(Ordering::Acquire);
        if cur & status::FINISHED != 0 {
            record_metric(spinner.count(), MetricKind::HandleLaneDep);
            return LaneDependencyResult::Ready;
        }
        if cur == status::NOT_STARTED {
            if start_processing_lane(n, smallvec![dep]) {
                record_metric(spinner.count(), MetricKind::HandleLaneDep);
                return LaneDependencyResult::StartedByThisThread;
            }
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
        if n
            .status_extra
            .compare_exchange_weak(cur, want, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
        {
            lane_pd_ref(n).dependents.push(dep);
            n.status_extra
                .fetch_and(!status::DEPS_LOCK, Ordering::Release);
            record_metric(spinner.count(), MetricKind::HandleLaneDep);
            return LaneDependencyResult::StartedByOtherThread;
        }
    }
}
