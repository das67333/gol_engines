//! Parallel GC sweep phase: walks every bucket chain in parallel.
//!
//! `is_dead(entry)` returns `true` for entries to remove (pushed to a per-thread
//! free list) and `false` for survivors kept in the chain. The callback may reset
//! live entries as a side effect. Must run after [`GcMarkExecutor`] and after all
//! executor threads have joined.

use crate::quadtree::hashtable::{ConcurrentHashTable, HashtableSlot, NULL_IDX, ThreadState};
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

        let per_thread_live: Vec<usize> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..threads_cnt)
                .map(|tid| {
                    let start = tid * buckets_per_thread;
                    let end = (start + buckets_per_thread).min(bucket_count);
                    scope.spawn(move || sweep_range(table, tid, start, end, is_dead))
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });

        self.table
            .length
            .set(per_thread_live.iter().sum());

        println!("Time spent on gc sweep executor: {:?}", timer.elapsed());
    }
}

fn sweep_range<E: HashtableSlot, F: Fn(&E) -> bool + Sync>(
    table: &ConcurrentHashTable<E>,
    tid: usize,
    start: usize,
    end: usize,
    is_dead: &F,
) -> usize {
    let free_list = table.thread_states[tid].get();
    let mut live = 0usize;
    for bucket in start..end {
        live += sweep_bucket(table, bucket, free_list, is_dead);
    }
    live
}

fn sweep_bucket<E: HashtableSlot, F: Fn(&E) -> bool>(
    table: &ConcurrentHashTable<E>,
    bucket: usize,
    free_list: *mut ThreadState,
    is_dead: &F,
) -> usize {
    let mut live = 0usize;
    let mut new_head = NULL_IDX;
    let mut cur = table.buckets[bucket].load(Ordering::Relaxed);
    while cur != NULL_IDX {
        let entry = table.get(cur);
        let next = entry.next().load(Ordering::Relaxed);
        if is_dead(entry) {
            push_free(entry, free_list, cur);
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

fn push_free<E: HashtableSlot>(entry: &E, free_list: *mut ThreadState, idx: u32) {
    // SAFETY: `free_list` is this thread's `ThreadState`; bucket ranges are disjoint.
    let old_head = unsafe { (*free_list).free_list_head };
    entry.next().store(old_head, Ordering::Relaxed);
    unsafe { (*free_list).free_list_head = idx };
}
