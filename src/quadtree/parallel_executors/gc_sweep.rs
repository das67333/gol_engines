//! Parallel GC sweep phase: walks every bucket chain in parallel.
//!
//! `is_dead(entry)` returns `true` for entries to recycle in shared batches
//! and `false` for survivors kept in the chain. The callback may reset
//! live entries as a side effect. Must run after [`GcMarkExecutor`] and after all
//! executor threads have joined.

use crate::quadtree::hashtable::{
    ConcurrentHashTable, HashtableSlot, Idx, NULL_IDX, RECYCLE_BATCH_SIZE,
};
use std::sync::atomic::Ordering;

pub struct GcSweepExecutor<'a, E> {
    table: &'a mut ConcurrentHashTable<E>,
}

impl<'a, E: HashtableSlot> GcSweepExecutor<'a, E> {
    pub fn new(table: &'a mut ConcurrentHashTable<E>) -> Self {
        Self { table }
    }

    pub fn run(&mut self, is_dead: impl Fn(&E) -> bool + Sync) {
        let timer = std::time::Instant::now();
        let threads_cnt = self.table.thread_states.len();
        let bucket_count = self.table.buckets.len();
        let buckets_per_thread = bucket_count.div_ceil(threads_cnt);

        // SAFETY: reborrow as shared. `ConcurrentHashTable` is `Sync`
        // (`unsafe impl Sync`), so `&self` is `Send` across threads.
        // Each thread accesses disjoint bucket ranges and its own
        // `ThreadState`; no concurrent allocation is in flight.
        let table = &*self.table;
        let is_dead = &is_dead;

        let swept: Vec<(usize, Vec<Idx>)> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..threads_cnt)
                .map(|tid| {
                    let start = tid * buckets_per_thread;
                    let end = (start + buckets_per_thread).min(bucket_count);
                    scope.spawn(move || sweep_range(table, tid, start, end, is_dead))
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });

        let mut live = 0;
        let recycled = self.table.recycled_batches.get_mut().unwrap();
        for (count, batches) in swept {
            live += count;
            recycled.extend(batches);
        }
        self.table.length.set(live);

        println!("Time spent on gc sweep executor: {:?}", timer.elapsed());
    }
}

fn sweep_range<E: HashtableSlot, F: Fn(&E) -> bool + Sync>(
    table: &ConcurrentHashTable<E>,
    tid: usize,
    start: usize,
    end: usize,
    is_dead: &F,
) -> (usize, Vec<Idx>) {
    let mut free = FreeBatches::default();
    let mut head = table.take_local_free_list(tid);
    while head != NULL_IDX {
        let entry = table.get(head);
        let next = entry.next().load(Ordering::Relaxed);
        free.push(entry, head);
        head = next;
    }
    let mut live = 0usize;
    for bucket in start..end {
        live += sweep_bucket(table, bucket, &mut free, is_dead);
    }
    (live, free.finish())
}

fn sweep_bucket<E: HashtableSlot, F: Fn(&E) -> bool>(
    table: &ConcurrentHashTable<E>,
    bucket: usize,
    free: &mut FreeBatches,
    is_dead: &F,
) -> usize {
    let mut live = 0usize;
    let mut new_head = NULL_IDX;
    let mut cur = table.buckets[bucket].load(Ordering::Relaxed);
    while cur != NULL_IDX {
        let entry = table.get(cur);
        let next = entry.next().load(Ordering::Relaxed);
        if is_dead(entry) {
            free.push(entry, cur);
        } else {
            live += 1;
            entry.next().store(new_head, Ordering::Relaxed);
            new_head = cur;
        }
        cur = next;
    }
    table.buckets[bucket].store(new_head, Ordering::Relaxed);
    live
}

#[derive(Default)]
struct FreeBatches {
    head: Idx,
    len: usize,
    batches: Vec<Idx>,
}

impl FreeBatches {
    fn push<E: HashtableSlot>(&mut self, entry: &E, idx: Idx) {
        entry.next().store(self.head, Ordering::Relaxed);
        self.head = idx;
        self.len += 1;
        if self.len == RECYCLE_BATCH_SIZE {
            self.batches.push(self.head);
            self.head = NULL_IDX;
            self.len = 0;
        }
    }

    fn finish(mut self) -> Vec<Idx> {
        if self.head != NULL_IDX {
            self.batches.push(self.head);
        }
        self.batches
    }
}
