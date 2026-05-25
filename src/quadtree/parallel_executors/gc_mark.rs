//! Parallel GC mark phase using work-stealing.
//!
//! Each thread DFS-walks the quadtree from the given roots. `fetch_or(GC_MARK)`
//! serves as both the atomic mark and the already-visited check. Must run
//! before [`GcSweepExecutor`] and after all executor threads have joined.

use super::super::{
    LEAF_SIZE_LOG2,
    hashtable::{Idx, NodeStore},
    node::QuadTreeNode,
    status,
};
use crossbeam::deque::{Steal, Stealer, Worker};
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct GcMarkExecutor<'a, Meta: Default + Sync> {
    mem: &'a NodeStore<Meta>,
    roots: &'a [Idx],
    size_log2: u32,
    threads_cnt: usize,
}

impl<'a, Meta: Default + Sync> GcMarkExecutor<'a, Meta> {
    pub fn new(
        mem: &'a NodeStore<Meta>,
        roots: &'a [Idx],
        size_log2: u32,
        threads_cnt: usize,
    ) -> Self {
        Self {
            mem,
            roots,
            size_log2,
            threads_cnt,
        }
    }

    pub fn run(&self) {
        let timer = std::time::Instant::now();
        let (queues, stealers) = new_work_queues(self.threads_cnt);
        let pending = AtomicUsize::new(self.roots.len());
        seed_roots(&queues[0], self.roots, self.size_log2);

        std::thread::scope(|scope| {
            for queue in queues {
                let worker = MarkWorker {
                    mem: self.mem,
                    queue,
                    stealers: &stealers,
                    pending: &pending,
                };
                scope.spawn(move || worker.run());
            }
        });

        println!("Time spent on gc mark executor: {:?}", timer.elapsed());
    }
}

fn new_work_queues(threads_cnt: usize) -> (Vec<Worker<(Idx, u32)>>, Vec<Stealer<(Idx, u32)>>) {
    let mut queues = Vec::with_capacity(threads_cnt);
    let mut stealers = Vec::with_capacity(threads_cnt);
    for _ in 0..threads_cnt {
        let q = Worker::new_lifo();
        stealers.push(q.stealer());
        queues.push(q);
    }
    (queues, stealers)
}

fn seed_roots(queue: &Worker<(Idx, u32)>, roots: &[Idx], size_log2: u32) {
    for &root in roots {
        queue.push((root, size_log2));
    }
}

struct MarkWorker<'a, 'b, Meta: Default + Sync> {
    mem: &'a NodeStore<Meta>,
    queue: Worker<(Idx, u32)>,
    stealers: &'b [Stealer<(Idx, u32)>],
    pending: &'b AtomicUsize,
}

impl<Meta: Default + Sync> MarkWorker<'_, '_, Meta> {
    fn run(self) {
        loop {
            match self.next_item() {
                Some((idx, sl2)) => self.visit(idx, sl2),
                None if self.pending.load(Ordering::Relaxed) == 0 => break,
                None => std::thread::yield_now(),
            }
        }
    }

    fn next_item(&self) -> Option<(Idx, u32)> {
        self.queue.pop().or_else(|| {
            self.stealers.iter().find_map(|s| match s.steal() {
                Steal::Success(item) => Some(item),
                _ => None,
            })
        })
    }

    fn visit(&self, idx: Idx, sl2: u32) {
        let n = self.mem.get(idx);
        let prev = n.status.fetch_or(status::GC_MARK, Ordering::Relaxed);
        if prev & status::GC_MARK == 0 && sl2 > LEAF_SIZE_LOG2 {
            self.enqueue_children(n, prev, sl2);
        }
        self.pending.fetch_sub(1, Ordering::Relaxed);
    }

    fn enqueue_children(&self, n: &QuadTreeNode<Meta>, prev: u8, sl2: u32) {
        let child_sl2 = sl2 - 1;
        for child in n.parts() {
            self.pending.fetch_add(1, Ordering::Relaxed);
            self.queue.push((child, child_sl2));
        }
        if prev & status::FINISHED != 0 {
            self.pending.fetch_add(1, Ordering::Relaxed);
            self.queue.push((n.cache.get_value(), child_sl2));
        }
    }
}
