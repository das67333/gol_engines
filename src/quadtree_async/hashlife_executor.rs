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
    LEAF_SIZE, LEAF_SIZE_LOG2,
    hashlife::HashLifeEngineAsync,
    memory::{MemoryManager, MemoryManagerRef},
    node::{Dependents, NodeIdx, ProcessingData, QuadTreeNode},
    status,
};
use crossbeam::deque::{Steal, Stealer, Worker};
use smallvec::{SmallVec, smallvec};
use std::{
    hint, mem,
    sync::atomic::{AtomicU8, AtomicU64, Ordering},
    thread,
    time::Duration,
};

/// A unit of work representing a node to be processed.
struct Task {
    idx: NodeIdx,
    size_log2: u32,
}

impl Task {
    fn new(idx: NodeIdx, size_log2: u32) -> Self {
        Self { idx, size_log2 }
    }
}

static STEAL_ATTEMPTS_SUCCESS: AtomicU64 = AtomicU64::new(0);
static STEAL_ATTEMPTS_EMPTY: AtomicU64 = AtomicU64::new(0);
static STEAL_ATTEMPTS_RETRY: AtomicU64 = AtomicU64::new(0);

static STEAL_FROM_LAST_VICTIM_SUCCESS: AtomicU64 = AtomicU64::new(0);
static STEAL_FROM_LAST_VICTIM_FAIL: AtomicU64 = AtomicU64::new(0);

pub(super) struct TaskFetcher<'a, T: Send, F: Fn() -> bool, C: Fn() -> bool> {
    thread_idx: usize,
    queue: &'a Worker<T>,
    stealers: &'a [Stealer<T>],
    finish_condition: F,
    cancel_condition: C,
    last_victim: usize,
    rng: rand_chacha::ChaCha8Rng,
    rng_buffer: Vec<u32>,
}

impl<'a, T: Send, F: Fn() -> bool, C: Fn() -> bool> TaskFetcher<'a, T, F, C> {
    /// Number of tasks to steal at once when work-stealing.
    const STEAL_BATCH_SIZE: usize = 1;
    const RNG_BUFFER_SIZE: usize = 256;
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
            rng_buffer: Vec::with_capacity(Self::RNG_BUFFER_SIZE),
        }
    }

    /// Fetch a task from local queue or steal from other threads.
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
        if let Some(task) = self.try_steal(self.last_victim) {
            STEAL_FROM_LAST_VICTIM_SUCCESS.fetch_add(1, Ordering::Relaxed);
            return Some(task);
        }
        STEAL_FROM_LAST_VICTIM_FAIL.fetch_add(1, Ordering::Relaxed);

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
        if let Some(x) = self.rng_buffer.pop() {
            return x as usize;
        }
        self.rng_buffer.resize(Self::RNG_BUFFER_SIZE, 0);
        rand::Rng::fill(&mut self.rng, &mut self.rng_buffer[..]);
        for i in self.rng_buffer.iter_mut() {
            *i %= self.stealers.len() as u32 - 1;
            // skip current index
            if *i >= self.thread_idx as u32 {
                *i += 1;
            }
        }
        self.rng_buffer.pop().unwrap() as usize
    }

    fn try_steal(&self, victim_id: usize) -> Option<T> {
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

/// Parallel executor for Hashlife algorithm using work-stealing.
pub(super) struct HashLifeExecutor<'a, Extra: Default + Sync> {
    root: NodeIdx,
    size_log2: u32,
    generations_log2: u32,
    mem: &'a MemoryManager<Extra>,
}

impl<'a, Extra: Default + Sync> HashLifeExecutor<'a, Extra> {
    pub(super) fn new(base: &'a HashLifeEngineAsync<Extra>) -> Self {
        Self {
            root: base.root,
            size_log2: base.size_log2,
            generations_log2: base.generations_per_update_log2.unwrap(),
            mem: &base.mem,
        }
    }

    pub(super) fn run(&self, num_threads: usize) -> Option<NodeIdx> {
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

        thread::scope(|scope| {
            for (thread_idx, queue) in queues.into_iter().enumerate() {
                let executor_thread = ExecutorThread {
                    root_node,
                    generations_log2: self.generations_log2,
                    mem: self.mem.create_ref(thread_idx),
                    thread_idx,
                    queue,
                    stealers: &stealers,
                };
                scope.spawn(move || executor_thread.run());
            }
        });

        if self.mem.exceeds_load_factor() {
            return None;
        }

        assert!(is_finished(&self.mem.get(self.root).status));
        println!("Nodes count: {}", self.mem.len());
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

        Some(root_node.cache.get_node_idx())
    }
}

struct ExecutorThread<'a, Extra: Default + Sync> {
    root_node: &'a QuadTreeNode<Extra>,
    generations_log2: u32,
    mem: MemoryManagerRef<'a, Extra>,
    thread_idx: usize,
    queue: Worker<Task>,
    stealers: &'a [Stealer<Task>],
}

impl<'a, Extra: Default + Sync> ExecutorThread<'a, Extra> {
    fn run(&self) {
        let mut fetcher = TaskFetcher::new(
            self.thread_idx,
            &self.queue,
            self.stealers,
            || is_finished(&self.root_node.status),
            || self.mem.exceeds_load_factor(),
        );

        while let Some(task) = fetcher.fetch_task() {
            self.process_task(task);
        }
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
        let data = n.cache.get_ref();
        if let Some(result) = self.update_node(&task, n.parts(), data) {
            n.cache.set_node_idx(result);
            let mut dependents = SmallVec::new();
            mem::swap(&mut data.dependents, &mut dependents);
            guard.finish(); // Mark as FINISHED
            unsafe { drop(Box::from_raw(data)) } // Free ProcessingData
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
    fn update_node(
        &self,
        task: &Task,
        parts: [NodeIdx; 4],
        data: &mut ProcessingData,
    ) -> Option<NodeIdx> {
        let both_stages = self.generations_log2 + 2 >= task.size_log2;
        let [nw, ne, sw, se] = parts;
        if task.size_log2 == LEAF_SIZE_LOG2 + 1 {
            // base case: node consists of leaves
            let steps = if both_stages {
                LEAF_SIZE / 2
            } else {
                1 << self.generations_log2
            };
            return Some(self.update_leaves(nw, ne, sw, se, steps));
        }

        if data.mask4_waiting == 0 {
            // arr4 is not ready
            if !both_stages {
                data.arr = self.nine_children_disjoint(nw, ne, sw, se, task.size_log2 - 1);
            } else {
                if data.mask9_waiting == 0 {
                    data.arr = self.nine_children_overlapping(nw, ne, sw, se);
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
                            *x = d.cache.get_node_idx();
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

            let arr4 = self.four_children_overlapping(&data.arr);
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
                    *x = d.cache.get_node_idx();
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
                let dep_data = n.cache.get_ref();
                dep_data.waiting_cnt -= 1;
                dep_data.waiting_cnt
            };
            if waiting_cnt == 0 {
                self.queue.push(Task::new(dependent, task.size_log2 + 1));
            }
        }
    }

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
    fn update_leaves(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        steps: u64,
    ) -> NodeIdx {
        let [nw, ne, sw, se] = [nw, ne, sw, se].map(|x| self.mem.get(x).leaf_cells());

        let mut src = [0; 16];
        for i in 0..8 {
            src[i] = u16::from_le_bytes([nw[i], ne[i]]);
            src[i + 8] = u16::from_le_bytes([sw[i], se[i]]);
        }
        let mut dst = [0; 16];

        for t in 1..=steps as usize {
            for y in t..16 - t {
                dst[y] = Self::update_row(src[y - 1], src[y], src[y + 1]);
            }
            std::mem::swap(&mut src, &mut dst);
        }

        let arr: [u16; 8] = src[4..12].try_into().unwrap();
        self.mem
            .find_or_create_leaf_from_u64(u64::from_le_bytes(arr.map(|x| (x >> 4) as u8)))
    }

    /// Create 9 overlapping children from a 2×2 block of nodes.
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
    fn nine_children_overlapping(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
    ) -> [NodeIdx; 9] {
        let [nw_, ne_, sw_, se_] = [nw, ne, sw, se].map(|x| self.mem.get(x));
        [
            nw,
            self.mem.find_or_create_node(nw_.ne, ne_.nw, nw_.se, ne_.sw),
            ne,
            self.mem.find_or_create_node(nw_.sw, nw_.se, sw_.nw, sw_.ne),
            self.mem.find_or_create_node(nw_.se, ne_.sw, sw_.ne, se_.nw),
            self.mem.find_or_create_node(ne_.sw, ne_.se, se_.nw, se_.ne),
            sw,
            self.mem.find_or_create_node(sw_.ne, se_.nw, sw_.se, se_.sw),
            se,
        ]
    }

    /// Create 9 non-overlapping children from a 2×2 block of nodes.
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
    fn nine_children_disjoint(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        size_log2: u32,
    ) -> [NodeIdx; 9] {
        let [
            [nwnw, nwne, nwsw, nwse],
            [nenw, nene, nesw, nese],
            [swnw, swne, swsw, swse],
            [senw, sene, sesw, sese],
        ] = [nw, ne, sw, se].map(|x| self.mem.get(x).parts().map(|y| self.mem.get(y)));

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
                self.mem.find_or_create_node(nw.se, ne.sw, sw.ne, se.nw)
            } else {
                self.mem.find_or_create_leaf_from_parts(
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
    fn four_children_overlapping(&self, arr: &[NodeIdx; 9]) -> [NodeIdx; 4] {
        [
            self.mem.find_or_create_node(arr[0], arr[1], arr[3], arr[4]),
            self.mem.find_or_create_node(arr[1], arr[2], arr[4], arr[5]),
            self.mem.find_or_create_node(arr[3], arr[4], arr[6], arr[7]),
            self.mem.find_or_create_node(arr[4], arr[5], arr[7], arr[8]),
        ]
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
fn start_processing_node<Extra: Default + Sync>(
    node: &QuadTreeNode<Extra>,
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
pub(super) fn atomic_transition_loop(a: &AtomicU8, from: u8, to: u8) {
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
fn handle_dependency<Extra: Default + Sync>(
    n: &QuadTreeNode<Extra>,
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
                n.cache.get_ref().dependents.push(task.idx);
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
