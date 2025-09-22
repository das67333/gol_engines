use super::{
    hashlife::HashLifeEngineAsync, status, MemoryManager, NodeIdx, LEAF_SIZE, LEAF_SIZE_LOG2,
};
use smallvec::{smallvec, SmallVec};
use std::{
    alloc::{alloc, dealloc, Layout},
    sync::atomic::Ordering,
};

struct Task {
    node: NodeIdx,
    size_log2: u32,
}

type Dependents = SmallVec<[NodeIdx; 2]>;

#[derive(Clone, Default)]
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
        let mut queue = Vec::new();
        {
            // initialize first task
            queue.push(Task {
                node: self.root,
                size_log2: self.size_log2,
            });
            let n = self.mem.get(self.root);
            let status_processing = Self::build_status_processing(smallvec![]);
            n.status.store(status_processing, Ordering::Relaxed);
        }

        while let Some(task) = queue.pop() {
            let n = self.mem.get(task.node);

            let both_stages = self.generations_log2 + 2 >= task.size_log2;
            let result = if task.size_log2 == LEAF_SIZE_LOG2 + 1 {
                // base case: node consists of leaves
                let steps = if both_stages {
                    LEAF_SIZE / 2
                } else {
                    1 << self.generations_log2
                };
                self.update_leaves(n.nw, n.ne, n.sw, n.se, steps)
            } else {
                let data =
                    unsafe { &mut *(n.status.load(Ordering::Relaxed) as *mut ProcessingData) };

                if data.mask4_waiting == 0 {
                    // arr4 is not ready
                    if !both_stages {
                        data.arr =
                            self.nine_children_disjoint(n.nw, n.ne, n.sw, n.se, task.size_log2 - 1);
                    } else {
                        if data.mask9_waiting == 0 {
                            data.arr = self.nine_children_overlapping(n.nw, n.ne, n.sw, n.se);
                            data.mask9_waiting = 0b1_1111_1111;
                        }

                        let mut waiting_cnt = 0;
                        for (i, x) in data.arr.iter_mut().enumerate() {
                            if data.mask9_waiting & (1 << i) == 0 {
                                continue;
                            }

                            let node = self.mem.get(*x);
                            let status = node.status.load(Ordering::Relaxed);
                            if status == status::CACHED {
                                data.mask9_waiting &= !(1 << i);
                                *x = unsafe { *node.cache.get() };
                                continue;
                            }

                            waiting_cnt += 1;
                            if status == status::NOT_CACHED {
                                queue.push(Task {
                                    node: *x,
                                    size_log2: task.size_log2 - 1,
                                });
                                let status_processing =
                                    Self::build_status_processing(smallvec![task.node]);
                                node.status.store(status_processing, Ordering::Relaxed);
                                continue;
                            }

                            // node we need is already processing
                            let pd = unsafe { &mut *(status as *mut ProcessingData) };
                            pd.dependents.push(task.node);
                        }

                        if data.mask9_waiting != 0 {
                            data.waiting_cnt = waiting_cnt;
                            // node is waiting its dependencies
                            continue;
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

                    let node = self.mem.get(*x);
                    let status = node.status.load(Ordering::Relaxed);
                    if status == status::CACHED {
                        data.mask4_waiting &= !(1 << i);
                        *x = unsafe { *node.cache.get() };
                        continue;
                    }

                    waiting_cnt += 1;
                    if status == status::NOT_CACHED {
                        queue.push(Task {
                            node: *x,
                            size_log2: task.size_log2 - 1,
                        });
                        let status_processing = Self::build_status_processing(smallvec![task.node]);
                        node.status.store(status_processing, Ordering::Relaxed);
                        continue;
                    }

                    // node we need is already processing
                    let pd = unsafe { &mut *(status as *mut ProcessingData) };
                    pd.dependents.push(task.node);
                }

                if data.mask4_waiting != 0 {
                    data.waiting_cnt = waiting_cnt;
                    continue;
                }

                self.mem
                    .find_or_create_node(data.arr[0], data.arr[1], data.arr[2], data.arr[3])
            };

            unsafe { *n.cache.get() = result };
            let old_status = n.status.swap(status::CACHED, Ordering::Relaxed); // TODO: mem order?
            let pd = unsafe { &mut *(old_status as *mut ProcessingData) };
            for &dependent in pd.dependents.iter() {
                let n = self.mem.get(dependent);
                let data_ref =
                    unsafe { &mut *(n.status.load(Ordering::Relaxed) as *mut ProcessingData) };
                data_ref.waiting_cnt -= 1;
                if data_ref.waiting_cnt == 0 {
                    queue.push(Task {
                        node: dependent,
                        size_log2: task.size_log2 + 1,
                    });
                }
            }
            unsafe { dealloc(old_status as *mut _, Layout::new::<ProcessingData>()) };
        }

        println!(
            "Nodes count: {}",
            crate::quadtree_async::statistics::LENGTH_GLOBAL_COUNT[0].load(Ordering::Relaxed)
        );

        let n = self.mem.get(self.root);
        assert_eq!(n.status.load(Ordering::Relaxed), status::CACHED);
        unsafe { *n.cache.get() }
    }

    fn build_status_processing(dependents: Dependents) -> usize {
        unsafe {
            let ptr = alloc(Layout::new::<ProcessingData>()) as *mut _;
            let pd = ProcessingData {
                dependents,
                ..Default::default()
            };
            std::ptr::write(ptr, pd);
            ptr as usize
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
