//! Paused-update roots and queue reconstruction. Every worker has joined before entry.

use super::*;
use std::sync::atomic::AtomicU16;

pub(in crate::quadtree) struct PausedWork {
    pub(in crate::quadtree) roots: Vec<(Idx, u32)>,
    pub(super) tasks: Vec<ReadyTask>,
    root_finished: bool,
}

impl PausedWork {
    pub(in crate::quadtree) fn can_resume(&self) -> bool {
        self.root_finished || !self.tasks.is_empty()
    }
}

impl StreamLifeExecutor<'_> {
    pub(in crate::quadtree) fn paused_work(&self) -> PausedWork {
        let mut paused = PausedWork {
            roots: vec![(self.biroot.0, self.size_log2), (self.biroot.1, self.size_log2)],
            tasks: Vec::new(),
            root_finished: false,
        };
        let mem = &self.engine.base.mem;
        let bicache = &self.engine.bicache;
        let root_idx = bicache.entry(self.biroot);
        let root = bicache.get(root_idx);
        if is_finished(root.status()) {
            let (a, b) = root.payload().get_value();
            paused.roots.extend([(a, self.size_log2 - 1), (b, self.size_log2 - 1)]);
            paused.root_finished = true;
            return paused;
        }
        let mut pending = vec![ReadyTask::Bi(BiTask { entry_idx: root_idx, size_log2: self.size_log2 })];
        let mut seen_nodes = ahash::AHashSet::new();
        while let Some(task) = pending.pop() {
            let roots_begin = paused.roots.len();
            match task {
                ReadyTask::Hash(task) => {
                    let node = mem.get(task.idx);
                    if node.status.load(Ordering::Relaxed) != status::PENDING || !seen_nodes.insert(task.idx) { continue; }
                    paused.roots.push((task.idx, task.size_log2));
                    // SAFETY: workers joined; PENDING owns this live payload.
                    let data = unsafe { &*node.cache.get_ptr::<HashProcessingData<Dependent>>() };
                    unsafe { data.paused_work() }.retained_roots(task.size_log2, &mut paused.roots);
                    if normalize_waiting(&data.waiting_cnt) == 0 { paused.tasks.push(ReadyTask::Hash(task)); }
                },
                ReadyTask::Bi(task) => {
                    let entry = bicache.get(task.entry_idx);
                    // GC_MARK also makes repeated visits skip this pending pair.
                    if entry.status().load(Ordering::Relaxed) != status::PENDING { continue; }
                    entry.status().fetch_or(status::GC_MARK, Ordering::Relaxed);
                    let (a, b) = entry.key();
                    paused.roots.extend([(a, task.size_log2), (b, task.size_log2)]);
                    // SAFETY: workers joined; PENDING owns this live payload.
                    let data = unsafe { &*entry.payload().get_ptr::<BiProcessingData>() };
                    let work = unsafe { data.paused_work() };
                    work.retained_roots(task.size_log2, &mut paused.roots);
                    if work.phase == BiPhase::Recursive {
                        let mask = if work.mask4_waiting != 0 { work.mask4_waiting } else { work.mask9_waiting };
                        for i in 0..9 {
                            if mask & (1 << i) != 0 {
                                if let Some(entry_idx) = bicache.find((work.arr0[i], work.arr1[i])) {
                                    let child = bicache.get(entry_idx);
                                    if is_finished(child.status()) {
                                        // Its notification can precede the parent's next scan.
                                        // Keep the result even while the parent's mask still holds its input.
                                        let (a, b) = child.payload().get_value();
                                        paused.roots.extend([(a, task.size_log2 - 2), (b, task.size_log2 - 2)]);
                                    } else {
                                        pending.push(ReadyTask::Bi(BiTask { entry_idx, size_log2: task.size_log2 - 1 }));
                                    }
                                }
                            }
                        }
                    }
                    if normalize_waiting(&data.waiting_cnt) == 0 { paused.tasks.push(ReadyTask::Bi(task)); }
                },
            }
            // Input and scratch roots also cover direct HashLife dependencies,
            // including both universes and the base phase's merged node.
            for &(idx, size_log2) in &paused.roots[roots_begin..] {
                if mem.get(idx).status.load(Ordering::Relaxed) == status::PENDING && !seen_nodes.contains(&idx) {
                    pending.push(ReadyTask::Hash(Task::new(idx, size_log2)));
                }
            }
        }
        paused
    }
}

// Cancellation may interrupt a binode's scan before its final bias subtraction.
fn normalize_waiting(counter: &AtomicU16) -> u16 {
    let count = counter.load(Ordering::Relaxed);
    let count = if count >= WAITING_BIAS { count - WAITING_BIAS } else { count };
    counter.store(count, Ordering::Relaxed);
    count
}

impl BiWork {
    fn retained_roots(&self, size_log2: u32, roots: &mut Vec<(Idx, u32)>) {
        match self.phase {
            BiPhase::Entry => {},
            BiPhase::Solitonic | BiPhase::Base => {
                if self.phase == BiPhase::Base { roots.push((self.arr0[0], size_log2)); }
                roots.extend(self.hash_results.iter().filter(|&&idx| idx != 0).map(|&idx| (idx, size_log2 - 1)));
            },
            BiPhase::Recursive => {
                let (count, waiting) = if self.mask4_waiting != 0 {
                    (4, self.mask4_waiting)
                } else {
                    (9, self.mask9_waiting)
                };
                for i in 0..count {
                    let level = size_log2 - if waiting & (1 << i) != 0 { 1 } else { 2 };
                    roots.extend([self.arr0[i], self.arr1[i]].into_iter().filter(|&idx| idx != 0).map(|idx| (idx, level)));
                }
            },
        }
    }
}
