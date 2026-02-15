//! # Unified Parallel Executor
//!
//! Work-stealing parallel executor for both HashLife and StreamLife algorithms.
//!
//! ## Architecture
//!
//! The executor uses thread-local LIFO queues with work-stealing for load balancing:
//! - Each thread has its own `Worker<Task>` queue
//! - When a thread runs out of work, it steals from other threads via `Stealer`
//! - No global queue is used - all tasks go directly to thread-local queues
//!
//! ## Task Types
//!
//! Two task variants coexist in the same queues:
//! - **Node tasks**: standard HashLife node computations (used by both engines)
//! - **BiNode tasks**: StreamLife binode pair computations (StreamLife only)
//!
//! ## Status State Machine
//!
//! Each node/entry progresses through these states during parallel processing:
//!
//! ```text
//!     ┌──────────────────────┐
//!     │    NOT_STARTED (0)   │ ◄── Initial state
//!     └──────────┬───────────┘
//!                │
//!                │ CAS(NOT_STARTED → PROCESSING)
//!                │ Only one thread claims the node
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

use super::{
    LEAF_SIZE, LEAF_SIZE_LOG2,
    hashlife::HashLifeEngine,
    hashtable::{BinodeCache, BinodeCacheRef, Idx, NodeStore, NodeStoreRef},
    node::QuadTreeNode,
    streamlife::StreamLifeEngine,
};
use algorithm::*;
use crossbeam::deque::{Steal, Stealer, Worker};
use smallvec::{SmallVec, smallvec};
use std::{
    hint, mem,
    sync::atomic::{AtomicU8, AtomicU64, Ordering},
    thread,
    time::Duration,
};

mod status {
    pub(super) const NOT_STARTED: u8 = 0;
    pub(super) const PROCESSING: u8 = 1;
    pub(super) const PENDING: u8 = 2;
    pub(super) const FINISHED: u8 = 3;
}

/// Tag bit for binode dependents stored in a node's `ProcessingData.dependents`.
/// When a binode registers as a dependent of a node, it stores
/// `entry_idx | BINODE_DEP_TAG`. The MSB distinguishes binode from node dependents.
const BINODE_DEP_TAG: Idx = 1 << 31;

// ---------------------------------------------------------------------------
// Task types
// ---------------------------------------------------------------------------

/// A unit of work in the unified executor.
#[derive(Clone, Copy)]
enum Task {
    /// Standard HashLife node computation.
    Node { idx: Idx, size_log2: u32 },
    /// StreamLife binode pair computation.
    BiNode { entry_idx: Idx, size_log2: u32 },
}

// ---------------------------------------------------------------------------
// Processing data for Node tasks (allocated on heap, stored via cache pointer)
// ---------------------------------------------------------------------------

/// List of nodes/entries waiting for this node's result.
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
    /// Nodes/entries that registered as dependents of this node.
    /// Entries use `idx | BINODE_DEP_TAG` to distinguish from node dependents.
    dependents: Dependents,
}

// ---------------------------------------------------------------------------
// Processing data for BiNode tasks
// ---------------------------------------------------------------------------

/// Phase of a binode task's computation.
///
/// Tracks where a binode task is in its lifecycle so that when it is resumed
/// after dependencies complete, it knows what post-processing to perform.
#[derive(Default, Clone, Copy, PartialEq, Eq)]
enum BiPhase {
    /// Initial entry: check solitonic, base-case, or set up recursive decomposition.
    #[default]
    Init,
    /// Waiting for 1-2 node tasks submitted for the solitonic fast-path.
    WaitSolitonic,
    /// Waiting for 1 node task submitted for the base-case fast-path.
    WaitBaseCase,
    /// Normal recursive 9+4 decomposition (both-stages or single-stage).
    Recursive,
}

/// Temporary data allocated during binode processing.
///
/// Heap-allocated when processing starts, freed when entry reaches FINISHED state.
/// Stored via pointer in the cache entry's payload field.
#[derive(Default)]
struct BiProcessingData {
    /// Current processing phase.
    phase: BiPhase,
    /// Intermediate child node results for universe 0 (BESZEL).
    arr0: [Idx; 9],
    /// Intermediate child node results for universe 1 (ULQOMA).
    arr1: [Idx; 9],
    /// Bitmask: bit `i` set if child pair `i` (among first 9) is not yet computed.
    mask9_waiting: u32,
    /// Bitmask: bit `i` set if child pair `i` (among first 4) is not yet computed.
    mask4_waiting: u32,
    /// Count of dependencies still being computed. Entry can resume when this reaches 0.
    waiting_cnt: u32,
    /// Entries that registered as dependents of this entry.
    /// Notified when this entry finishes.
    dependents: SmallVec<[Idx; 2]>,
}

// ---------------------------------------------------------------------------
// Steal counters (debug/profiling)
// ---------------------------------------------------------------------------

static STEAL_ATTEMPTS_SUCCESS: AtomicU64 = AtomicU64::new(0);
static STEAL_ATTEMPTS_EMPTY: AtomicU64 = AtomicU64::new(0);
static STEAL_ATTEMPTS_RETRY: AtomicU64 = AtomicU64::new(0);

static STEAL_FROM_LAST_VICTIM_SUCCESS: AtomicU64 = AtomicU64::new(0);
static STEAL_FROM_LAST_VICTIM_FAIL: AtomicU64 = AtomicU64::new(0);

// ---------------------------------------------------------------------------
// TaskFetcher: work-stealing task acquisition
// ---------------------------------------------------------------------------

struct TaskFetcher<'a, F: Fn() -> bool, C: Fn() -> bool> {
    thread_idx: usize,
    queue: &'a Worker<Task>,
    stealers: &'a [Stealer<Task>],
    finish_condition: F,
    cancel_condition: C,
    last_victim: usize,
    rng: rand_chacha::ChaCha8Rng,
    rng_buffer: Vec<u32>,
}

impl<'a, F: Fn() -> bool, C: Fn() -> bool> TaskFetcher<'a, F, C> {
    const STEAL_BATCH_SIZE: usize = 1;
    const RNG_BUFFER_SIZE: usize = 256;
    const INITIAL_WAIT_DURATION: Duration = Duration::from_micros(100);
    const MAX_WAIT_DURATION: Duration = Duration::from_millis(100);

    fn new(
        thread_idx: usize,
        queue: &'a Worker<Task>,
        stealers: &'a [Stealer<Task>],
        finish_condition: F,
        cancel_condition: C,
    ) -> Self {
        use rand::SeedableRng;
        Self {
            thread_idx,
            queue,
            stealers,
            finish_condition,
            cancel_condition,
            last_victim: 0,
            rng: rand_chacha::ChaCha8Rng::from_os_rng(),
            rng_buffer: Vec::with_capacity(Self::RNG_BUFFER_SIZE),
        }
    }

    /// Fetch a task from local queue or steal from other threads.
    fn fetch_task(&mut self) -> Option<Task> {
        if (self.cancel_condition)() {
            return None;
        }

        if let Some(task) = self.queue.pop() {
            return Some(task);
        }

        if self.stealers.len() <= 1 {
            return None;
        }

        if let Some(task) = self.try_steal(self.last_victim) {
            STEAL_FROM_LAST_VICTIM_SUCCESS.fetch_add(1, Ordering::Relaxed);
            return Some(task);
        }
        STEAL_FROM_LAST_VICTIM_FAIL.fetch_add(1, Ordering::Relaxed);

        let mut duration = Self::INITIAL_WAIT_DURATION;
        while !(self.finish_condition)() && !(self.cancel_condition)() {
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
        if let Some(x) = self.rng_buffer.pop() {
            return x as usize;
        }
        self.rng_buffer.resize(Self::RNG_BUFFER_SIZE, 0);
        rand::Rng::fill(&mut self.rng, &mut self.rng_buffer[..]);
        for i in self.rng_buffer.iter_mut() {
            *i %= self.stealers.len() as u32 - 1;
            if *i >= self.thread_idx as u32 {
                *i += 1;
            }
        }
        self.rng_buffer.pop().unwrap() as usize
    }

    fn try_steal(&self, victim_id: usize) -> Option<Task> {
        loop {
            match self.stealers[victim_id]
                .steal_batch_with_limit_and_pop(self.queue, Self::STEAL_BATCH_SIZE)
            {
                Steal::Success(task) => {
                    STEAL_ATTEMPTS_SUCCESS.fetch_add(1, Ordering::Relaxed);
                    return Some(task);
                }
                Steal::Empty => {
                    STEAL_ATTEMPTS_EMPTY.fetch_add(1, Ordering::Relaxed);
                    return None;
                }
                Steal::Retry => {
                    STEAL_ATTEMPTS_RETRY.fetch_add(1, Ordering::Relaxed);
                    continue;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Executor: top-level parallel executor
// ---------------------------------------------------------------------------

/// Unified parallel executor for HashLife and StreamLife algorithms.
pub(super) struct Executor<'a, Meta: Default + Sync> {
    mem: &'a NodeStore<Meta>,
    root: Idx,
    size_log2: u32,
    generations_log2: u32,
    /// Present only for StreamLife mode.
    stream: Option<StreamContext<'a>>,
}

struct StreamContext<'a> {
    engine: &'a StreamLifeEngine,
    biroot_entry_idx: Idx,
}

impl<'a, Meta: Default + Sync> Executor<'a, Meta> {
    /// Create an executor for pure HashLife.
    pub(super) fn new_hashlife(base: &'a HashLifeEngine<Meta>) -> Self {
        Self {
            mem: &base.mem,
            root: base.root,
            size_log2: base.size_log2,
            generations_log2: base.generations_per_update_log2.unwrap(),
            stream: None,
        }
    }

    /// Run the executor in HashLife mode. Returns the computed root result.
    pub(super) fn run_hashlife(&self, num_threads: usize) -> Option<Idx> {
        let root_node = self.mem.get(self.root);
        start_processing_node(root_node, smallvec![]);

        let mut queues = Vec::with_capacity(num_threads);
        let mut stealers = Vec::with_capacity(num_threads);
        for _ in 0..num_threads {
            let queue = Worker::new_lifo();
            stealers.push(queue.stealer());
            queues.push(queue);
        }

        queues[0].push(Task::Node {
            idx: self.root,
            size_log2: self.size_log2,
        });

        let root_status = &root_node.status;
        thread::scope(|scope| {
            for (thread_idx, queue) in queues.into_iter().enumerate() {
                let et = ExecutorThread {
                    root_status,
                    generations_log2: self.generations_log2,
                    mem: self.mem.create_ref(thread_idx),
                    queue,
                    stealers: &stealers,
                    thread_idx,
                    stream: None,
                };
                scope.spawn(move || et.run());
            }
        });

        if self.mem.exceeds_load_factor() {
            return None;
        }

        assert!(is_finished(root_status));
        print_stats("HashLife", || {
            println!("Nodes count: {}", self.mem.len());
        });

        Some(root_node.cache.get_value())
    }
}

impl<'a> Executor<'a, u64> {
    /// Create an executor for StreamLife.
    pub(super) fn new_streamlife(
        engine: &'a StreamLifeEngine,
        biroot: (Idx, Idx),
        size_log2: u32,
    ) -> Self {
        let biroot_entry_idx = engine.bicache.entry(biroot);
        Self {
            mem: &engine.base.mem,
            root: 0,
            size_log2,
            generations_log2: engine.base.generations_per_update_log2.unwrap(),
            stream: Some(StreamContext {
                engine,
                biroot_entry_idx,
            }),
        }
    }

    /// Run the executor in StreamLife mode. Returns the computed biroot result.
    pub(super) fn run_streamlife(&self, num_threads: usize) -> Option<(Idx, Idx)> {
        let stream = self.stream.as_ref().unwrap();
        let bicache = &stream.engine.bicache;
        let biroot_entry_idx = stream.biroot_entry_idx;
        let root_status = bicache.get(biroot_entry_idx).status();

        start_processing_entry(bicache, biroot_entry_idx, smallvec![]);

        let mut queues = Vec::with_capacity(num_threads);
        let mut stealers = Vec::with_capacity(num_threads);
        for _ in 0..num_threads {
            let queue = Worker::new_lifo();
            stealers.push(queue.stealer());
            queues.push(queue);
        }

        queues[0].push(Task::BiNode {
            entry_idx: biroot_entry_idx,
            size_log2: self.size_log2,
        });

        thread::scope(|scope| {
            for (thread_idx, queue) in queues.into_iter().enumerate() {
                let et = ExecutorThread {
                    root_status,
                    generations_log2: self.generations_log2,
                    mem: self.mem.create_ref(thread_idx),
                    queue,
                    stealers: &stealers,
                    thread_idx,
                    stream: Some(ThreadStreamContext {
                        engine: stream.engine,
                        bicache_ref: bicache.create_ref(thread_idx),
                    }),
                };
                scope.spawn(move || et.run());
            }
        });

        if self.mem.exceeds_load_factor() || bicache.exceeds_load_factor() {
            return None;
        }

        assert!(is_finished(root_status));
        print_stats("StreamLife", || {
            println!(
                "Nodes count: {}, BiCache count: {}",
                self.mem.len(),
                bicache.len()
            );
        });

        Some(bicache.get(biroot_entry_idx).payload.get_value())
    }
}

fn print_stats(label: &str, extra: impl FnOnce()) {
    extra();
    let _ = label;
    println!(
        "STEAL_ATTEMPTS_SUCCESS: {}",
        STEAL_ATTEMPTS_SUCCESS.load(Ordering::Relaxed)
    );
    println!(
        "STEAL_ATTEMPTS_EMPTY: {}",
        STEAL_ATTEMPTS_EMPTY.load(Ordering::Relaxed)
    );
    println!(
        "STEAL_ATTEMPTS_RETRY: {}",
        STEAL_ATTEMPTS_RETRY.load(Ordering::Relaxed)
    );
    println!(
        "STEAL_FROM_LAST_VICTIM_SUCCESS: {}",
        STEAL_FROM_LAST_VICTIM_SUCCESS.load(Ordering::Relaxed)
    );
    println!(
        "STEAL_FROM_LAST_VICTIM_FAIL: {}",
        STEAL_FROM_LAST_VICTIM_FAIL.load(Ordering::Relaxed)
    );
}

// ---------------------------------------------------------------------------
// Per-thread executor
// ---------------------------------------------------------------------------

struct ExecutorThread<'a, Meta: Default + Sync> {
    root_status: &'a AtomicU8,
    generations_log2: u32,
    mem: NodeStoreRef<'a, Meta>,
    thread_idx: usize,
    queue: Worker<Task>,
    stealers: &'a [Stealer<Task>],
    stream: Option<ThreadStreamContext<'a>>,
}

struct ThreadStreamContext<'a> {
    engine: &'a StreamLifeEngine,
    bicache_ref: BinodeCacheRef<'a>,
}

impl<'a, Meta: Default + Sync> ExecutorThread<'a, Meta> {
    fn run(&self) {
        let stream = &self.stream;
        let mut fetcher = TaskFetcher::new(
            self.thread_idx,
            &self.queue,
            self.stealers,
            || is_finished(self.root_status),
            || {
                self.mem.exceeds_load_factor()
                    || stream
                        .as_ref()
                        .is_some_and(|s| s.bicache_ref.exceeds_load_factor())
            },
        );

        while let Some(task) = fetcher.fetch_task() {
            match task {
                Task::Node { idx, size_log2 } => self.process_node_task(idx, size_log2),
                Task::BiNode {
                    entry_idx,
                    size_log2,
                } => self.process_binode_task(entry_idx, size_log2),
            }
        }
    }

    // -----------------------------------------------------------------------
    // Node task processing (HashLife algorithm)
    // -----------------------------------------------------------------------

    /// Process a single node task: compute the node's result or wait for dependencies.
    fn process_node_task(&self, idx: Idx, size_log2: u32) {
        let n = self.mem.get(idx);
        let mut guard = ProcessingGuard::new(&n.status);
        let data: &mut ProcessingData = n.cache.get_ref();
        if let Some(result) = self.update_node(idx, size_log2, n.parts(), data) {
            n.cache.set_value(result);
            let mut dependents = SmallVec::new();
            mem::swap(&mut data.dependents, &mut dependents);
            guard.finish();
            unsafe { drop(Box::from_raw(data as *mut ProcessingData)) }
            self.notify_node_dependents(size_log2, dependents);
        }
    }

    /// Compute node result by processing its children/dependencies.
    ///
    /// Returns `Some(result)` if computation completes, `None` if waiting for dependencies.
    fn update_node(
        &self,
        idx: Idx,
        size_log2: u32,
        parts: [Idx; 4],
        data: &mut ProcessingData,
    ) -> Option<Idx> {
        let both_stages = self.generations_log2 + 2 >= size_log2;
        let [nw, ne, sw, se] = parts;
        if size_log2 == LEAF_SIZE_LOG2 + 1 {
            let steps = if both_stages {
                LEAF_SIZE / 2
            } else {
                1 << self.generations_log2
            };
            return Some(update_leaves(&self.mem, nw, ne, sw, se, steps));
        }

        if data.mask4_waiting == 0 {
            if !both_stages {
                data.arr = nine_children_disjoint(&self.mem, nw, ne, sw, se, size_log2 - 1);
            } else {
                if data.mask9_waiting == 0 {
                    data.arr = nine_children_overlapping(&self.mem, nw, ne, sw, se);
                    data.mask9_waiting = 0b1_1111_1111;
                }

                let mut waiting_cnt = 0;
                for (i, x) in data.arr.iter_mut().enumerate() {
                    if data.mask9_waiting & (1 << i) == 0 {
                        continue;
                    }
                    let d = self.mem.get(*x);
                    match handle_dependency(d, idx) {
                        DependencyHandlingResult::Ready => {
                            data.mask9_waiting &= !(1 << i);
                            *x = d.cache.get_value();
                        }
                        DependencyHandlingResult::StartedByThisThread => {
                            self.queue.push(Task::Node {
                                idx: *x,
                                size_log2: size_log2 - 1,
                            });
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

            let arr4 = four_children_overlapping(&self.mem, &data.arr);
            data.arr[..4].copy_from_slice(&arr4);
            data.mask4_waiting = 0b1111;
        }

        let mut waiting_cnt = 0;
        for (i, x) in data.arr.iter_mut().take(4).enumerate() {
            if data.mask4_waiting & (1 << i) == 0 {
                continue;
            }
            let d = self.mem.get(*x);
            match handle_dependency(d, idx) {
                DependencyHandlingResult::Ready => {
                    data.mask4_waiting &= !(1 << i);
                    *x = d.cache.get_value();
                }
                DependencyHandlingResult::StartedByThisThread => {
                    self.queue.push(Task::Node {
                        idx: *x,
                        size_log2: size_log2 - 1,
                    });
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

    /// Notify dependents of a completed node.
    ///
    /// Handles both node dependents (untagged) and binode dependents (tagged with
    /// `BINODE_DEP_TAG`). Node dependents are re-queued at `size_log2 + 1`;
    /// binode dependents are re-queued at the **same** `size_log2` since the binode
    /// is at the same tree level as the solitonic/base-case node it depends on.
    fn notify_node_dependents(&self, size_log2: u32, dependents: Dependents) {
        for &dep_id in dependents.iter() {
            if dep_id & BINODE_DEP_TAG != 0 {
                // BiNode dependent
                let entry_idx = dep_id & !BINODE_DEP_TAG;
                let stream = self.stream.as_ref().unwrap();
                let entry = stream.bicache_ref.get(entry_idx);
                let status = entry.status();
                let waiting_cnt = {
                    let _guard = ProcessingGuard::new(status);
                    let dep_data: &mut BiProcessingData = entry.payload.get_ref();
                    dep_data.waiting_cnt -= 1;
                    dep_data.waiting_cnt
                };
                if waiting_cnt == 0 {
                    self.queue.push(Task::BiNode {
                        entry_idx,
                        size_log2,
                    });
                }
            } else {
                // Node dependent
                let n = self.mem.get(dep_id);
                let waiting_cnt = {
                    let _guard = ProcessingGuard::new(&n.status);
                    let dep_data: &mut ProcessingData = n.cache.get_ref();
                    dep_data.waiting_cnt -= 1;
                    dep_data.waiting_cnt
                };
                if waiting_cnt == 0 {
                    self.queue.push(Task::Node {
                        idx: dep_id,
                        size_log2: size_log2 + 1,
                    });
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // BiNode task processing (StreamLife algorithm)
    // -----------------------------------------------------------------------

    /// Process a single binode task.
    fn process_binode_task(&self, entry_idx: Idx, size_log2: u32) {
        let stream = self.stream.as_ref().unwrap();
        let entry = stream.bicache_ref.get(entry_idx);
        let status = entry.status();
        let mut guard = ProcessingGuard::new(status);
        let data: &mut BiProcessingData = entry.payload.get_ref();
        let idx = entry.key();

        if let Some(result) = self.update_binode(entry_idx, idx, size_log2, data) {
            entry.payload.set_value(result);
            let mut dependents = SmallVec::new();
            mem::swap(&mut data.dependents, &mut dependents);
            guard.finish();
            unsafe { drop(Box::from_raw(data as *mut BiProcessingData)) };
            self.notify_binode_dependents(size_log2, dependents);
        }
    }

    /// Compute binode result or identify dependencies.
    ///
    /// Returns `Some(result)` if computation completes, `None` if waiting for dependencies.
    ///
    /// Four cases:
    /// 1. **Solitonic** (`WaitSolitonic`): Two universes are provably non-interacting.
    ///    Submit node tasks for each universe, wait, then post-process lane assignment.
    /// 2. **Base case** (`WaitBaseCase`, `size_log2 == LEAF_SIZE_LOG2 + 2`): Merge
    ///    universes, submit one node task, wait, then split result back.
    /// 3. **Recursive case** (`Recursive`): Process 9+4 child binode pairs.
    fn update_binode(
        &self,
        parent_entry_idx: Idx,
        idx: (Idx, Idx),
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let stream = self.stream.as_ref().unwrap();
        let engine = stream.engine;

        // --- Resume from WaitSolitonic ---
        if data.phase == BiPhase::WaitSolitonic {
            return Some(self.finish_solitonic(idx, size_log2, data));
        }

        // --- Resume from WaitBaseCase ---
        if data.phase == BiPhase::WaitBaseCase {
            return Some(self.finish_base_case(idx, size_log2, data));
        }

        // --- Init phase: check fast-paths ---
        if data.phase == BiPhase::Init {
            // Solitonic: two universes don't interact, compute independently
            if is_solitonic(engine, idx, size_log2) {
                return self.start_solitonic(parent_entry_idx, idx, size_log2, data);
            }

            // Base case: merge universes and run standard HashLife
            if size_log2 == LEAF_SIZE_LOG2 + 2 {
                return self.start_base_case(parent_entry_idx, idx, size_log2, data);
            }

            // Recursive case: set up children for both universes
            data.phase = BiPhase::Recursive;
            let generations_log2 = self.generations_log2;
            let both_stages = generations_log2 + 2 >= size_log2;
            let n0 = self.mem.get(idx.0);
            let n1 = self.mem.get(idx.1);

            if both_stages {
                data.arr0 = nine_children_overlapping(&self.mem, n0.nw, n0.ne, n0.sw, n0.se);
                data.arr1 = nine_children_overlapping(&self.mem, n1.nw, n1.ne, n1.sw, n1.se);
                data.mask9_waiting = 0b1_1111_1111;
            } else {
                data.arr0 =
                    nine_children_disjoint(&self.mem, n0.nw, n0.ne, n0.sw, n0.se, size_log2 - 1);
                data.arr1 =
                    nine_children_disjoint(&self.mem, n1.nw, n1.ne, n1.sw, n1.se, size_log2 - 1);
            }
        }

        // --- Recursive path (shared between Init-fallthrough and Recursive resume) ---
        self.update_binode_recursive(parent_entry_idx, size_log2, data)
    }

    /// Recursive 9+4 decomposition for binode tasks.
    fn update_binode_recursive(
        &self,
        parent_entry_idx: Idx,
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let stream = self.stream.as_ref().unwrap();
        let engine = stream.engine;

        // Stage 1: Wait for 9 overlapping children (if both_stages)
        if data.mask4_waiting == 0 && data.mask9_waiting != 0 {
            let mut waiting_cnt = 0;
            for i in 0..9 {
                if data.mask9_waiting & (1 << i) == 0 {
                    continue;
                }
                let child_key = (data.arr0[i], data.arr1[i]);
                let child_idx = stream.bicache_ref.entry(child_key);

                match handle_bi_dependency(&engine.bicache, child_idx, parent_entry_idx) {
                    BiDependencyResult::Ready => {
                        data.mask9_waiting &= !(1 << i);
                        let val = stream.bicache_ref.get(child_idx).payload.get_value();
                        data.arr0[i] = val.0;
                        data.arr1[i] = val.1;
                    }
                    BiDependencyResult::StartedByThisThread => {
                        self.queue.push(Task::BiNode {
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
            let arr40 = four_children_overlapping(&engine.base.mem, &data.arr0);
            let arr41 = four_children_overlapping(&engine.base.mem, &data.arr1);
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
                let child_idx = stream.bicache_ref.entry(child_key);

                match handle_bi_dependency(&engine.bicache, child_idx, parent_entry_idx) {
                    BiDependencyResult::Ready => {
                        data.mask4_waiting &= !(1 << i);
                        let val = stream.bicache_ref.get(child_idx).payload.get_value();
                        data.arr0[i] = val.0;
                        data.arr1[i] = val.1;
                    }
                    BiDependencyResult::StartedByThisThread => {
                        self.queue.push(Task::BiNode {
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

    // -----------------------------------------------------------------------
    // Async solitonic path
    // -----------------------------------------------------------------------

    /// Begin the solitonic fast-path: submit Node tasks for both universes.
    ///
    /// Stores original `idx` in `data.arr0[0..2]` for post-processing.
    /// Returns `Some` immediately if both nodes are already finished.
    fn start_solitonic(
        &self,
        parent_entry_idx: Idx,
        idx: (Idx, Idx),
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let tagged_dep = parent_entry_idx | BINODE_DEP_TAG;

        // Store original indices for post-processing
        data.arr0[0] = idx.0;
        data.arr0[1] = idx.1;

        let mut waiting_cnt: u32 = 0;

        let n0 = self.mem.get(idx.0);
        match handle_dependency(n0, tagged_dep) {
            DependencyHandlingResult::Ready => {}
            DependencyHandlingResult::StartedByThisThread => {
                self.queue.push(Task::Node {
                    idx: idx.0,
                    size_log2,
                });
                waiting_cnt += 1;
            }
            DependencyHandlingResult::StartedByOtherThread => {
                waiting_cnt += 1;
            }
        }

        let n1 = self.mem.get(idx.1);
        match handle_dependency(n1, tagged_dep) {
            DependencyHandlingResult::Ready => {}
            DependencyHandlingResult::StartedByThisThread => {
                self.queue.push(Task::Node {
                    idx: idx.1,
                    size_log2,
                });
                waiting_cnt += 1;
            }
            DependencyHandlingResult::StartedByOtherThread => {
                waiting_cnt += 1;
            }
        }

        if waiting_cnt == 0 {
            return Some(self.finish_solitonic(idx, size_log2, data));
        }

        data.phase = BiPhase::WaitSolitonic;
        data.waiting_cnt = waiting_cnt;
        None
    }

    /// Complete the solitonic fast-path: read node results and assign lanes.
    fn finish_solitonic(
        &self,
        _idx: (Idx, Idx),
        size_log2: u32,
        data: &BiProcessingData,
    ) -> (Idx, Idx) {
        let stream = self.stream.as_ref().unwrap();
        let engine = stream.engine;

        let orig0 = data.arr0[0];
        let orig1 = data.arr0[1];
        let i1 = self.mem.get(orig0).cache.get_value();
        let i2 = self.mem.get(orig1).cache.get_value();

        let b = engine.base.blank_nodes.get(size_log2);
        if orig0 == b || orig1 == b {
            let (i3, ind3) = if orig0 == b { (i2, orig1) } else { (i1, orig0) };
            let lanes = node2lanes(engine, ind3, size_log2);
            let b = engine.base.blank_nodes.get(size_log2 - 1);
            if lanes & 0xf0 != 0 { (b, i3) } else { (i3, b) }
        } else {
            (i1, i2)
        }
    }

    // -----------------------------------------------------------------------
    // Async base-case path
    // -----------------------------------------------------------------------

    /// Begin the base-case fast-path: merge universes, submit one Node task.
    ///
    /// Stores `hnode2` in `data.arr0[0]` for post-processing.
    /// Returns `Some` immediately if the merged node is already finished.
    fn start_base_case(
        &self,
        parent_entry_idx: Idx,
        idx: (Idx, Idx),
        size_log2: u32,
        data: &mut BiProcessingData,
    ) -> Option<(Idx, Idx)> {
        let stream = self.stream.as_ref().unwrap();
        let engine = stream.engine;
        let tagged_dep = parent_entry_idx | BINODE_DEP_TAG;

        let hnode2 = engine.merge_universes(idx, size_log2);
        data.arr0[0] = hnode2;

        let n = self.mem.get(hnode2);
        match handle_dependency(n, tagged_dep) {
            DependencyHandlingResult::Ready => {
                return Some(self.finish_base_case(idx, size_log2, data));
            }
            DependencyHandlingResult::StartedByThisThread => {
                self.queue.push(Task::Node {
                    idx: hnode2,
                    size_log2,
                });
            }
            DependencyHandlingResult::StartedByOtherThread => {}
        }

        data.phase = BiPhase::WaitBaseCase;
        data.waiting_cnt = 1;
        None
    }

    /// Complete the base-case fast-path: read node result and split universes.
    fn finish_base_case(
        &self,
        _idx: (Idx, Idx),
        size_log2: u32,
        data: &BiProcessingData,
    ) -> (Idx, Idx) {
        let stream = self.stream.as_ref().unwrap();
        let engine = stream.engine;

        let hnode2 = data.arr0[0];
        let i3 = self.mem.get(hnode2).cache.get_value();
        let b = engine.base.blank_nodes.get(size_log2 - 1);

        if i3 != b {
            let lanes = node2lanes(engine, hnode2, size_log2);
            if lanes & 0xf0 != 0 { (b, i3) } else { (i3, b) }
        } else {
            (b, b)
        }
    }

    // -----------------------------------------------------------------------
    // BiNode dependency notification
    // -----------------------------------------------------------------------

    /// Notify dependent binode entries that this binode has completed.
    fn notify_binode_dependents(&self, size_log2: u32, dependents: SmallVec<[Idx; 2]>) {
        let stream = self.stream.as_ref().unwrap();
        for &dependent in dependents.iter() {
            let entry = stream.bicache_ref.get(dependent);
            let status = entry.status();
            let waiting_cnt = {
                let _guard = ProcessingGuard::new(status);
                let dep_data: &mut BiProcessingData = entry.payload.get_ref();
                dep_data.waiting_cnt -= 1;
                dep_data.waiting_cnt
            };
            if waiting_cnt == 0 {
                self.queue.push(Task::BiNode {
                    entry_idx: dependent,
                    size_log2: size_log2 + 1,
                });
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Check if a status field indicates FINISHED.
fn is_finished(status: &AtomicU8) -> bool {
    status.load(Ordering::Acquire) == status::FINISHED
}

/// Initialize a node for processing by transitioning NOT_STARTED → PROCESSING → PENDING.
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
struct ProcessingGuard<'a> {
    status: &'a AtomicU8,
    released: bool,
}

impl<'a> ProcessingGuard<'a> {
    fn new(status: &'a AtomicU8) -> Self {
        atomic_transition_loop(status, status::PENDING, status::PROCESSING);
        Self {
            status,
            released: false,
        }
    }

    fn finish(&mut self) {
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

/// Result of attempting to handle a node dependency.
enum DependencyHandlingResult {
    Ready,
    StartedByThisThread,
    StartedByOtherThread,
}

/// Handle a node dependency: check if ready, start processing, or register as dependent.
fn handle_dependency<Meta: Default + Sync>(
    n: &QuadTreeNode<Meta>,
    dependent_id: Idx,
) -> DependencyHandlingResult {
    let status = n.status.load(Ordering::Acquire);
    if status == status::FINISHED {
        return DependencyHandlingResult::Ready;
    }

    if status == status::NOT_STARTED && start_processing_node(n, smallvec![dependent_id]) {
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
                    .push(dependent_id);
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

// ---------------------------------------------------------------------------
// BiNode dependency helpers
// ---------------------------------------------------------------------------

/// Initialize a cache entry for processing.
fn start_processing_entry(
    bicache: &BinodeCache,
    entry_idx: Idx,
    dependents: SmallVec<[Idx; 2]>,
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
        return false;
    }

    let pd = BiProcessingData {
        dependents,
        ..Default::default()
    };
    entry.payload.set_ptr(Box::into_raw(Box::new(pd)));
    status.store(status::PENDING, Ordering::Release);
    true
}

/// Result of attempting to handle a binode dependency.
enum BiDependencyResult {
    Ready,
    StartedByThisThread,
    StartedByOtherThread,
}

/// Handle a binode dependency: check if ready, claim for processing, or register as dependent.
fn handle_bi_dependency(
    bicache: &BinodeCache,
    child_idx: Idx,
    parent_entry_idx: Idx,
) -> BiDependencyResult {
    let child_entry = bicache.get(child_idx);
    let status = child_entry.status();
    let status_value = status.load(Ordering::Acquire);

    if status_value == status::FINISHED {
        return BiDependencyResult::Ready;
    }

    if status_value == status::NOT_STARTED
        && start_processing_entry(bicache, child_idx, smallvec![parent_entry_idx])
    {
        return BiDependencyResult::StartedByThisThread;
    }

    loop {
        match status.compare_exchange_weak(
            status::PENDING,
            status::PROCESSING,
            Ordering::Acquire,
            Ordering::Acquire,
        ) {
            Ok(_) => {
                let child_data: &mut BiProcessingData = child_entry.payload.get_ref();
                child_data.dependents.push(parent_entry_idx);
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

// ---------------------------------------------------------------------------
// Algorithm primitives (HashLife tree decomposition + StreamLife lane analysis)
// ---------------------------------------------------------------------------

mod algorithm {
    use super::{
        super::{
            LEAF_SIZE_LOG2,
            hashtable::{Idx, NodeAccess},
            streamlife::StreamLifeEngine,
        },
        status,
    };
    use std::{hint::spin_loop, sync::atomic::Ordering};

    type NodeStore = super::super::hashtable::NodeStore<u64>;

    // -----------------------------------------------------------------------
    // HashLife tree decomposition
    // -----------------------------------------------------------------------

    /// Apply Conway's Game of Life rules to a row of cells.
    ///
    /// Uses bit-parallel computation to update 16 cells simultaneously.
    /// Implements the standard B3/S23 rule (born with 3 neighbors, survive with 2-3).
    fn update_row(row_prev: u16, row_curr: u16, row_next: u16) -> u16 {
        let b = row_prev;
        let a = b << 1;
        let c = b >> 1;
        let i = row_curr;
        let h = i << 1;
        let d = i >> 1;
        let f = row_next;
        let g = f << 1;
        let e = f >> 1;

        let ab0 = a ^ b;
        let ab1 = a & b;
        let cd0 = c ^ d;
        let cd1 = c & d;

        let ef0 = e ^ f;
        let ef1 = e & f;
        let gh0 = g ^ h;
        let gh1 = g & h;

        let ad0 = ab0 ^ cd0;
        let ad1 = (ab1 ^ cd1) ^ (ab0 & cd0);
        let ad2 = ab1 & cd1;

        let eh0 = ef0 ^ gh0;
        let eh1 = (ef1 ^ gh1) ^ (ef0 & gh0);
        let eh2 = ef1 & gh1;

        let ah0 = ad0 ^ eh0;
        let xx = ad0 & eh0;
        let yy = ad1 ^ eh1;
        let ah1 = xx ^ yy;
        let ah23 = (ad2 | eh2) | (ad1 & eh1) | (xx & yy);
        let z = !ah23 & ah1;
        let i2 = !ah0 & z;
        let i3 = ah0 & z;
        (i & i2) | i3
    }

    /// Update a 2x2 block of leaf nodes by simulating `steps` generations.
    ///
    /// This is the base case of Hashlife recursion. Combines 4 leaf nodes (8x8 each)
    /// into a 16x16 grid, simulates forward, and extracts the center 8x8 result.
    /// `nw`, `ne`, `sw`, `se` must be leaves.
    pub(super) fn update_leaves<Meta: Default + Sync>(
        mem: &impl NodeAccess<Meta>,
        nw: Idx,
        ne: Idx,
        sw: Idx,
        se: Idx,
        steps: u64,
    ) -> Idx {
        let [nw, ne, sw, se] = [nw, ne, sw, se].map(|x| mem.get(x).leaf_cells());

        let mut src = [0; 16];
        for i in 0..8 {
            src[i] = u16::from_le_bytes([nw[i], ne[i]]);
            src[i + 8] = u16::from_le_bytes([sw[i], se[i]]);
        }
        let mut dst = [0; 16];

        for t in 1..=steps as usize {
            for y in t..16 - t {
                dst[y] = update_row(src[y - 1], src[y], src[y + 1]);
            }
            std::mem::swap(&mut src, &mut dst);
        }

        let arr: [u16; 8] = src[4..12].try_into().unwrap();
        mem.find_or_create_leaf_from_u64(u64::from_le_bytes(arr.map(|x| (x >> 4) as u8)))
    }

    /// Create 9 overlapping children from a 2x2 block of nodes.
    ///
    /// ```text
    /// Input: 2×2 block         Output: 9 overlapping children
    /// ┌─────┬─────┐            ┌─────┬─────┬─────┐
    /// │ NW  │ NE  │            │  0  │  1  │  2  │
    /// │     │     │            │(NW) │(mid)│(NE) │
    /// ├─────┼─────┤            ├─────┼─────┼─────┤
    /// │ SW  │ SE  │            │  3  │  4  │  5  │
    /// │     │     │            │(mid)│(ctr)│(mid)│
    /// └─────┴─────┘            ├─────┼─────┼─────┤
    ///                          │  6  │  7  │  8  │
    ///                          │(SW) │(mid)│(SE) │
    ///                          └─────┴─────┴─────┘
    ///
    /// Children 0,2,6,8 are the original input nodes.
    /// Children 1,3,5,7 are formed from overlapping edges.
    /// Child 4 is formed from the center where all four inputs meet.
    /// ```
    pub(super) fn nine_children_overlapping<Meta: Default + Sync>(
        mem: &impl NodeAccess<Meta>,
        nw: Idx,
        ne: Idx,
        sw: Idx,
        se: Idx,
    ) -> [Idx; 9] {
        let [nw_, ne_, sw_, se_] = [nw, ne, sw, se].map(|x| mem.get(x));
        [
            nw,
            mem.find_or_create_node(nw_.ne, ne_.nw, nw_.se, ne_.sw),
            ne,
            mem.find_or_create_node(nw_.sw, nw_.se, sw_.nw, sw_.ne),
            mem.find_or_create_node(nw_.se, ne_.sw, sw_.ne, se_.nw),
            mem.find_or_create_node(ne_.sw, ne_.se, se_.nw, se_.ne),
            sw,
            mem.find_or_create_node(sw_.ne, se_.nw, sw_.se, se_.sw),
            se,
        ]
    }

    /// Create 9 non-overlapping children from a 2x2 block of nodes.
    ///
    /// ```text
    /// Input: 2×2 block          Each input node has 4 children:
    /// ┌──────┬──────┐           ┌───┬───┐
    /// │  NW  │  NE  │           │nw │ne │
    /// │      │      │           ├───┼───┤
    /// ├──────┼──────┤           │sw │se │
    /// │  SW  │  SE  │           └───┴───┘
    /// │      │      │
    /// └──────┴──────┘
    ///
    /// Output: 9 non-overlapping children formed from centers:
    /// ┌─────┬─────┬─────┐
    /// │  0  │  1  │  2  │  ← 0: from NW's children, 1: from NW+NE, 2: from NE's children
    /// ├─────┼─────┼─────┤
    /// │  3  │  4  │  5  │  ← 3: from NW+SW, 4: from all four, 5: from NE+SE
    /// ├─────┼─────┼─────┤
    /// │  6  │  7  │  8  │  ← 6: from SW's children, 7: from SW+SE, 8: from SE's children
    /// └─────┴─────┴─────┘
    ///
    /// Each output is formed by taking center regions from the input nodes' children.
    /// ```
    pub(super) fn nine_children_disjoint<Meta: Default + Sync>(
        mem: &impl NodeAccess<Meta>,
        nw: Idx,
        ne: Idx,
        sw: Idx,
        se: Idx,
        size_log2: u32,
    ) -> [Idx; 9] {
        let [
            [nwnw, nwne, nwsw, nwse],
            [nenw, nene, nesw, nese],
            [swnw, swne, swsw, swse],
            [senw, sene, sesw, sese],
        ] = [nw, ne, sw, se].map(|x| mem.get(x).parts().map(|y| mem.get(y)));

        [
            [nwnw, nwne, nwsw, nwse],
            [nwne, nenw, nwse, nesw],
            [nenw, nene, nesw, nese],
            [nwsw, nwse, swnw, swne],
            [nwse, nesw, swne, senw],
            [nesw, nese, senw, sene],
            [swnw, swne, swsw, swse],
            [swne, senw, swse, sesw],
            [senw, sene, sesw, sese],
        ]
        .map(|[nw, ne, sw, se]| {
            if size_log2 >= LEAF_SIZE_LOG2 + 2 {
                mem.find_or_create_node(nw.se, ne.sw, sw.ne, se.nw)
            } else {
                mem.find_or_create_leaf_from_parts(
                    nw.leaf_se(),
                    ne.leaf_sw(),
                    sw.leaf_ne(),
                    se.leaf_nw(),
                )
            }
        })
    }

    /// Combine 9 overlapping children into 4 final children.
    ///
    /// ```text
    /// Input:           Output:
    /// ┌───┬───┬───┐    ┌─────┬─────┐
    /// │ 0 │ 1 │ 2 │    │  A  │  B  │
    /// ├───┼───┼───┤    │     │     │
    /// │ 3 │ 4 │ 5 │    ├─────┼─────┤
    /// ├───┼───┼───┤    │  C  │  D  │
    /// │ 6 │ 7 │ 8 │    │     │     │
    /// └───┴───┴───┘    └─────┴─────┘
    ///
    /// A = combine(0,1,3,4)
    /// B = combine(1,2,4,5)
    /// C = combine(3,4,6,7)
    /// D = combine(4,5,7,8)
    /// ```
    pub(super) fn four_children_overlapping<Meta: Default + Sync>(
        mem: &impl NodeAccess<Meta>,
        arr: &[Idx; 9],
    ) -> [Idx; 4] {
        [
            mem.find_or_create_node(arr[0], arr[1], arr[3], arr[4]),
            mem.find_or_create_node(arr[1], arr[2], arr[4], arr[5]),
            mem.find_or_create_node(arr[3], arr[4], arr[6], arr[7]),
            mem.find_or_create_node(arr[4], arr[5], arr[7], arr[8]),
        ]
    }

    // -----------------------------------------------------------------------
    // StreamLife lane analysis
    // -----------------------------------------------------------------------

    /// Detect the direction of a glider from a 2x2 block of leaves.
    fn determine_direction(mem: &NodeStore, nw: Idx, ne: Idx, sw: Idx, se: Idx) -> u64 {
        let m = update_leaves(mem, nw, ne, sw, se, 4);
        let centre = u64::from_le_bytes(mem.get(m).leaf_cells());

        let [nw, ne, sw, se] =
            [nw, ne, sw, se].map(|x| u64::from_le_bytes(mem.get(x).leaf_cells()));

        let z64_centre_to_u64 = |x, y| {
            let xs = (4 + x) as u64;
            let ys = ((4 + y) << 3) as u64;
            let bitmask: u64 = (0x0101010101010101 << xs) - 0x0101010101010101;
            let left = (nw >> ys) | (sw << (64 - ys));
            let right = (ne >> ys) | (se << (64 - ys));
            ((right & bitmask) << (8 - xs)) | ((left & (!bitmask)) >> xs)
        };

        let mut dmap = 0;
        if centre == z64_centre_to_u64(-1, -1) {
            dmap |= 1
        } // SE
        if centre == z64_centre_to_u64(0, -2) {
            dmap |= 2
        } // S
        if centre == z64_centre_to_u64(1, -1) {
            dmap |= 4
        } // SW
        if centre == z64_centre_to_u64(2, 0) {
            dmap |= 8
        } // W
        if centre == z64_centre_to_u64(1, 1) {
            dmap |= 16
        } // NW
        if centre == z64_centre_to_u64(0, 2) {
            dmap |= 32
        } // N
        if centre == z64_centre_to_u64(-1, 1) {
            dmap |= 64
        } // NE
        if centre == z64_centre_to_u64(-2, 0) {
            dmap |= 128
        } // E

        let mut lmask = 0;
        if centre != 0 {
            if dmap & 170 != 0 {
                lmask |= 3;
            }
            if dmap & 85 != 0 {
                lmask |= 7;
            }
        }

        dmap | (lmask << 32)
    }

    /// Compute lane descriptors for a node. Thread-safe (uses CAS on `status_extra`).
    pub(super) fn node2lanes(engine: &StreamLifeEngine, idx: Idx, size_log2: u32) -> u64 {
        if idx == engine.base.blank_nodes.get(size_log2) {
            return 0xffff;
        }

        let n = engine.base.mem.get(idx);
        let status = n.status_extra.load(Ordering::Acquire);
        if status == status::FINISHED {
            return unsafe { *n.extra.get() };
        }

        if !(status == status::NOT_STARTED
            && n.status_extra
                .compare_exchange(
                    status::NOT_STARTED,
                    status::PROCESSING,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                )
                .is_ok())
        {
            while n.status_extra.load(Ordering::Acquire) != status::FINISHED {
                spin_loop();
            }
            return unsafe { *n.extra.get() };
        }

        if size_log2 == LEAF_SIZE_LOG2 + 1 {
            let extra = determine_direction(&engine.base.mem, n.nw, n.ne, n.sw, n.se);
            unsafe { *n.extra.get() = extra };
            n.status_extra.store(status::FINISHED, Ordering::Release);
            return extra;
        }

        let (nw, ne, sw, se) = {
            let n = engine.base.mem.get(idx);
            (n.nw, n.ne, n.sw, n.se)
        };

        let mut childlanes = [0u64; 9];
        let mut adml: u64 = 0xff;

        if adml != 0 {
            childlanes[0] = node2lanes(engine, nw, size_log2 - 1);
            adml &= childlanes[0];
        }
        if adml != 0 {
            childlanes[2] = node2lanes(engine, ne, size_log2 - 1);
            adml &= childlanes[2];
        }
        if adml != 0 {
            childlanes[6] = node2lanes(engine, sw, size_log2 - 1);
            adml &= childlanes[6];
        }
        if adml != 0 {
            childlanes[8] = node2lanes(engine, se, size_log2 - 1);
            adml &= childlanes[8];
        }
        if adml == 0 {
            unsafe { *n.extra.get() = 0 };
            n.status_extra.store(status::FINISHED, Ordering::Release);
            return 0;
        }

        if size_log2 == LEAF_SIZE_LOG2 + 2 {
            let tlx = {
                let nw = engine.base.mem.get(nw);
                [nw.nw, nw.ne, nw.sw, nw.se]
                    .map(|x| u64::from_le_bytes(engine.base.mem.get(x).leaf_cells()))
            };
            let trx = {
                let ne = engine.base.mem.get(ne);
                [ne.nw, ne.ne, ne.sw, ne.se]
                    .map(|x| u64::from_le_bytes(engine.base.mem.get(x).leaf_cells()))
            };
            let blx = {
                let sw = engine.base.mem.get(sw);
                [sw.nw, sw.ne, sw.sw, sw.se]
                    .map(|x| u64::from_le_bytes(engine.base.mem.get(x).leaf_cells()))
            };
            let brx = {
                let se = engine.base.mem.get(se);
                [se.nw, se.ne, se.sw, se.se]
                    .map(|x| u64::from_le_bytes(engine.base.mem.get(x).leaf_cells()))
            };

            let cc = [tlx[3], trx[2], blx[1], brx[0]];
            let tc = [tlx[1], trx[0], tlx[3], trx[2]];
            let bc = [blx[1], brx[0], blx[3], brx[2]];
            let cl = [tlx[2], tlx[3], blx[0], blx[1]];
            let cr = [trx[2], trx[3], brx[0], brx[1]];

            let prepared = |mem: &NodeStore, x: &[u64; 4]| {
                let nw = mem.find_or_create_leaf_from_u64(x[0]);
                let ne = mem.find_or_create_leaf_from_u64(x[1]);
                let sw = mem.find_or_create_leaf_from_u64(x[2]);
                let se = mem.find_or_create_leaf_from_u64(x[3]);
                mem.find_or_create_node(nw, ne, sw, se)
            };

            for (i, x) in [(1, &tc), (3, &cl), (4, &cc), (5, &cr), (7, &bc)] {
                childlanes[i] = node2lanes(engine, prepared(&engine.base.mem, x), size_log2 - 1);
            }
            adml &= childlanes[1] & childlanes[3] & childlanes[4] & childlanes[5] & childlanes[7];
        } else {
            let pptr_tl = engine.base.mem.get(nw);
            let pptr_tr = engine.base.mem.get(ne);
            let pptr_bl = engine.base.mem.get(sw);
            let pptr_br = engine.base.mem.get(se);
            let cc = [pptr_tl.se, pptr_tr.sw, pptr_bl.ne, pptr_br.nw];
            let tc = [pptr_tl.ne, pptr_tr.nw, pptr_tl.se, pptr_tr.sw];
            let bc = [pptr_bl.ne, pptr_br.nw, pptr_bl.se, pptr_br.sw];
            let cl = [pptr_tl.sw, pptr_tl.se, pptr_bl.nw, pptr_bl.ne];
            let cr = [pptr_tr.sw, pptr_tr.se, pptr_br.nw, pptr_br.ne];

            let prepared =
                |mem: &NodeStore, x: &[Idx; 4]| mem.find_or_create_node(x[0], x[1], x[2], x[3]);

            for (i, x) in [(1, &tc), (3, &cl), (4, &cc), (5, &cr), (7, &bc)] {
                childlanes[i] = node2lanes(engine, prepared(&engine.base.mem, x), size_log2 - 1);
            }
            adml &= childlanes[1] & childlanes[3] & childlanes[4] & childlanes[5] & childlanes[7];
        }
        for x in &mut childlanes {
            *x >>= 32;
        }
        let mut lanes = 0;

        let rotr32 = |x, y| (x >> y) | (x << (32 - y));
        let rotl32 = |x, y| (x << y) | (x >> (32 - y));

        let a: u64 = if size_log2 - LEAF_SIZE_LOG2 - 2 <= 4 {
            1 << (size_log2 - LEAF_SIZE_LOG2 - 2)
        } else {
            0
        };
        let a2 = (2 * a) & 31;

        if adml & 0x88 != 0 {
            lanes |= rotl32(childlanes[0] | childlanes[1] | childlanes[2], a);
            lanes |= childlanes[3] | childlanes[4] | childlanes[5];
            lanes |= rotr32(childlanes[6] | childlanes[7] | childlanes[8], a);
        }

        if adml & 0x44 != 0 {
            lanes |= rotl32(childlanes[0], a2);
            lanes |= rotl32(childlanes[3] | childlanes[1], a);
            lanes |= childlanes[6] | childlanes[4] | childlanes[2];
            lanes |= rotr32(childlanes[7] | childlanes[5], a);
            lanes |= rotr32(childlanes[8], a2);
        }

        if adml & 0x22 != 0 {
            lanes |= rotl32(childlanes[0] | childlanes[3] | childlanes[6], a);
            lanes |= childlanes[1] | childlanes[4] | childlanes[7];
            lanes |= rotr32(childlanes[2] | childlanes[5] | childlanes[8], a);
        }

        if adml & 0x11 != 0 {
            lanes |= rotl32(childlanes[2], a2);
            lanes |= rotl32(childlanes[1] | childlanes[5], a);
            lanes |= childlanes[0] | childlanes[4] | childlanes[8];
            lanes |= rotr32(childlanes[3] | childlanes[7], a);
            lanes |= rotr32(childlanes[6], a2);
        }

        let extra = adml | (lanes << 32);
        unsafe { *n.extra.get() = extra };
        n.status_extra.store(status::FINISHED, Ordering::Release);
        extra
    }

    /// Check if two universes are provably non-interacting (solitonic).
    pub(super) fn is_solitonic(engine: &StreamLifeEngine, idx: (Idx, Idx), size_log2: u32) -> bool {
        let lanes1 = node2lanes(engine, idx.0, size_log2);
        if lanes1 & 255 == 0 {
            return false;
        }
        let lanes2 = node2lanes(engine, idx.1, size_log2);
        if lanes2 & 255 == 0 {
            return false;
        }
        let commonlanes = (lanes1 & lanes2) >> 32;
        if commonlanes != 0 {
            return false;
        }
        (((lanes1 >> 4) & lanes2) | ((lanes2 >> 4) & lanes1)) & 15 != 0
    }
}
