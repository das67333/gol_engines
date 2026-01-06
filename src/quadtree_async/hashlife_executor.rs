use super::{
    hashlife::HashLifeEngineAsync, status, MemoryManager, NodeIdx, QuadTreeNode, LEAF_SIZE,
    LEAF_SIZE_LOG2,
};
use crossbeam_deque::{Injector, Steal, Stealer, Worker};
use smallvec::{smallvec, SmallVec};
use std::{
    hint,
    sync::atomic::{AtomicU8, AtomicUsize, Ordering},
    thread,
    time::Duration,
};

struct Task {
    idx: NodeIdx,
    size_log2: u32,
}

impl Task {
    fn new(idx: NodeIdx, size_log2: u32) -> Self {
        Self { idx, size_log2 }
    }
}

type Dependents = SmallVec<[NodeIdx; 2]>;

#[derive(Default)]
struct ProcessingData {
    arr: [NodeIdx; 9],
    mask9_waiting: u32,
    mask4_waiting: u32,
    waiting_cnt: u32,
    dependents: Dependents,
}

pub(super) struct HashLifeExecutor<'a, Extra: Default + Sync> {
    root: NodeIdx,
    size_log2: u32,
    generations_log2: u32,
    mem: &'a MemoryManager<Extra>,
}

static MAX_LEN: AtomicUsize = AtomicUsize::new(0);

type Queue<T> = Injector<T>;

impl<'a, Extra: Default + Sync> HashLifeExecutor<'a, Extra> {
    pub(super) fn new(base: &'a HashLifeEngineAsync<Extra>) -> Self {
        Self {
            root: base.root,
            size_log2: base.size_log2,
            generations_log2: base.generations_per_update_log2.unwrap(),
            mem: &base.mem,
        }
    }

    pub(super) fn run(&self) -> NodeIdx {
        // Get number of threads
        let num_threads = 4; //thread::available_parallelism().map(|n| n.get()).unwrap();

        // Create global injector queue
        let injector = Injector::new();

        // Create worker queues and stealers
        let mut workers = Vec::with_capacity(num_threads);
        let mut stealers = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let worker = Worker::new_lifo();
            let stealer = worker.stealer();
            workers.push(worker);
            stealers.push(stealer);
        }

        start_processing_node(self.mem.get(self.root), smallvec![]);
        injector.push(Task::new(self.root, self.size_log2));

        thread::scope(|scope| {
            for (thread_id, mut worker) in workers.into_iter().enumerate() {
                let injector = &injector;
                let stealers = &stealers;
                scope.spawn(move || self.worker_thread(thread_id, &mut worker, injector, stealers));
            }
        });

        println!(
            "Nodes count: {}",
            crate::quadtree_async::statistics::LENGTH_GLOBAL_COUNT[0].load(Ordering::SeqCst)
        );
        println!("Max queue len: {}", MAX_LEN.load(Ordering::SeqCst));
        assert!(is_finished(&self.mem.get(self.root).status));

        let n = self.mem.get(self.root);
        n.cache.get_node_idx()
    }

    fn worker_thread(
        &self,
        thread_id: usize,
        worker: &Worker<Task>,
        injector: &Injector<Task>,
        stealers: &[Stealer<Task>],
    ) {
        let root_status = &self.mem.get(self.root).status;
        loop {
            while let Some(task) = Self::fetch_task(thread_id, worker, injector, stealers) {
                // MAX_LEN.store(
                //     MAX_LEN.load(Ordering::SeqCst).max(injector.len()),
                //     Ordering::SeqCst,
                // );

                self.process_task(task, injector);
            }

            if is_finished(root_status) {
                return;
            }
            println!("No tasks found for thread {}", thread_id);
            thread::sleep(Duration::from_millis(10));
        }
    }

    fn fetch_task(
        thread_id: usize,
        worker: &Worker<Task>,
        injector: &Injector<Task>,
        stealers: &[Stealer<Task>],
    ) -> Option<Task> {
        // Try to get a task from local queue first
        worker.pop().or_else(|| {
            // Try to steal from global injector
            loop {
                match injector.steal_batch_and_pop(worker) {
                    Steal::Success(task) => return Some(task),
                    Steal::Empty => break,
                    Steal::Retry => continue,
                }
            }

            // TODO: randomize here?
            // Try to steal from other workers
            for (i, stealer) in stealers.iter().enumerate() {
                if i == thread_id {
                    continue;
                }

                loop {
                    match stealer.steal_batch_and_pop(worker) {
                        Steal::Success(task) => return Some(task),
                        Steal::Empty => break,
                        Steal::Retry => continue,
                    }
                }
            }

            None
        })
    }

    fn process_task(&self, task: Task, queue: &Queue<Task>) {
        let n = self.mem.get(task.idx);
        let mut guard = ProcessingGuard::new(&n.status);
        let data = get_mut_processing_data(n);
        if let Some(result) = self.update_node(&task, n.parts(), data, queue) {
            n.cache.set_node_idx(result);
            self.notify_dependents(&task, data, queue);
            unsafe { drop(Box::from_raw(data)) }
            guard.set_finished();
        }
    }

    fn update_node(
        &self,
        task: &Task,
        parts: [NodeIdx; 4],
        data: &mut ProcessingData,
        queue: &Queue<Task>,
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
                        DependencyHandlingResult::DependencyIsReady => {
                            data.mask9_waiting &= !(1 << i);
                            *x = d.cache.get_node_idx();
                        }
                        DependencyHandlingResult::StartedByThisThread => {
                            queue.push(Task::new(*x, task.size_log2 - 1));
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
                DependencyHandlingResult::DependencyIsReady => {
                    data.mask4_waiting &= !(1 << i);
                    *x = d.cache.get_node_idx();
                }
                DependencyHandlingResult::StartedByThisThread => {
                    queue.push(Task::new(*x, task.size_log2 - 1));
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

    fn notify_dependents(&self, task: &Task, data: &mut ProcessingData, queue: &Queue<Task>) {
        for &dependent in data.dependents.iter() {
            let n = self.mem.get(dependent);
            let _guard = ProcessingGuard::new(&n.status);
            let dep_data = get_mut_processing_data(n);
            dep_data.waiting_cnt -= 1;
            if dep_data.waiting_cnt == 0 {
                queue.push(Task::new(dependent, task.size_log2 + 1));
            }
        }
    }

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

    /// `nw`, `ne`, `sw`, `se` must be leaves
    pub(super) fn update_leaves(
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

    pub(super) fn nine_children_overlapping(
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

    pub(super) fn nine_children_disjoint(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        size_log2: u32,
    ) -> [NodeIdx; 9] {
        let [[nwnw, nwne, nwsw, nwse], [nenw, nene, nesw, nese], [swnw, swne, swsw, swse], [senw, sene, sesw, sese]] =
            [nw, ne, sw, se].map(|x| self.mem.get(x).parts().map(|y| self.mem.get(y)));

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

    pub(super) fn four_children_overlapping(&self, arr: &[NodeIdx; 9]) -> [NodeIdx; 4] {
        [
            self.mem.find_or_create_node(arr[0], arr[1], arr[3], arr[4]),
            self.mem.find_or_create_node(arr[1], arr[2], arr[4], arr[5]),
            self.mem.find_or_create_node(arr[3], arr[4], arr[6], arr[7]),
            self.mem.find_or_create_node(arr[4], arr[5], arr[7], arr[8]),
        ]
    }
}

fn get_mut_processing_data<Extra: Default + Sync>(node: &QuadTreeNode<Extra>) -> &mut ProcessingData {
    unsafe { &mut *(node.cache.get_ptr() as *mut _) }
}

fn is_finished(status: &AtomicU8) -> bool {
    status.load(Ordering::Relaxed) == status::FINISHED
}

fn start_processing_node<Extra: Default + Sync>(
    node: &QuadTreeNode<Extra>,
    dependents: Dependents,
) -> bool {
    if node
        .status
        .compare_exchange(
            status::NOT_STARTED,
            status::PROCESSING,
            Ordering::SeqCst,
            Ordering::SeqCst,
        )
        .is_err()
    {
        return false;
    }

    let pd = ProcessingData {
        dependents,
        ..Default::default()
    };
    node.cache.set_ptr(Box::into_raw(Box::new(pd)) as usize);
    node.status.store(status::PENDING, Ordering::SeqCst);
    true
}

fn atomic_transition(atomic: &AtomicU8, from: u8, to: u8, valid_states: &[u8]) {
    let mut current = atomic.load(Ordering::Relaxed);
    loop {
        while current != from {
            if !valid_states.contains(&current) {
                panic!("Invalid state: {}", current)
            }
            hint::spin_loop();
            current = atomic.load(Ordering::Relaxed);
        }

        match atomic.compare_exchange_weak(from, to, Ordering::AcqRel, Ordering::Relaxed) {
            Ok(_) => return,
            Err(actual) => current = actual,
        }
    }
}

struct ProcessingGuard<'a> {
    status: &'a AtomicU8,
    is_finished: bool,
}

impl<'a> ProcessingGuard<'a> {
    fn new(status: &'a AtomicU8) -> Self {
        atomic_transition(
            status,
            status::PENDING,
            status::PROCESSING,
            &[status::PROCESSING],
        );
        Self {
            status,
            is_finished: false,
        }
    }
}

impl<'a> ProcessingGuard<'a> {
    fn set_finished(&mut self) {
        self.is_finished = true;
    }
}

impl<'a> Drop for ProcessingGuard<'a> {
    fn drop(&mut self) {
        let final_status = if self.is_finished {
            status::FINISHED
        } else {
            status::PENDING
        };
        self.status.store(final_status, Ordering::SeqCst);
    }
}

enum DependencyHandlingResult {
    DependencyIsReady,
    StartedByThisThread,
    StartedByOtherThread,
}

fn handle_dependency<Extra: Default + Sync>(
    n: &QuadTreeNode<Extra>,
    task: &Task,
) -> DependencyHandlingResult {
    let status = n.status.load(Ordering::SeqCst);
    if status == status::FINISHED {
        return DependencyHandlingResult::DependencyIsReady;
    }

    if status == status::NOT_STARTED && start_processing_node(n, smallvec![task.idx]) {
        return DependencyHandlingResult::StartedByThisThread;
    }

    // node we need is already processing
    loop {
        match n.status.compare_exchange_weak(
            status::PENDING,
            status::PROCESSING,
            Ordering::SeqCst,
            Ordering::SeqCst,
        ) {
            Ok(_) => {
                let pd = get_mut_processing_data(n);
                pd.dependents.push(task.idx);
                n.status.store(status::PENDING, Ordering::SeqCst);
                return DependencyHandlingResult::StartedByOtherThread;
            }
            Err(status::FINISHED) => return DependencyHandlingResult::DependencyIsReady,
            Err(status::PROCESSING) => hint::spin_loop(),
            Err(value) => panic!("Unexpected status in append_dependent: {}", value),
        }
    }
}
