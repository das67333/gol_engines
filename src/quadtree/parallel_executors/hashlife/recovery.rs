//! Paused-update roots and queue reconstruction. Every worker has joined before entry.

use super::*;

impl<Meta: Default + Sync> HashLifeExecutor<'_, Meta> {
    pub(in crate::quadtree) fn paused_work(&self) -> PausedWork<Task> {
        let mut paused = PausedWork {
            roots: vec![(self.root, self.size_log2)],
            tasks: Vec::new(),
            root_finished: is_finished(&self.mem.get(self.root).status),
        };
        let mut seen = ahash::AHashSet::new();
        let mut cursor = 0;
        while cursor < paused.roots.len() {
            let (idx, size_log2) = paused.roots[cursor];
            cursor += 1;
            let node = self.mem.get(idx);
            if node.status.load(Ordering::Relaxed) != status::PENDING || !seen.insert(idx) {
                continue;
            }
            // SAFETY: workers joined; PENDING owns this live payload.
            let data = unsafe { &*node.cache.get_ptr::<HashProcessingData<Idx>>() };
            unsafe { data.paused_work() }.retained_roots(size_log2, &mut paused.roots);
            // HashLife scans finish before workers observe cancellation, so no bias remains.
            if data.waiting_cnt.load(Ordering::Relaxed) == 0 {
                paused.tasks.push(Task::new(idx, size_log2));
            }
        }
        paused
    }

    /// Drop pending payloads only when the update cannot resume. Workers have joined.
    pub(in crate::quadtree) fn discard_pending(&self) {
        self.mem.for_each_idx(|idx| {
            let node = self.mem.get(idx);
            if node.status.load(Ordering::Relaxed) == status::PENDING {
                // SAFETY: PENDING owns the original Box pointer; all workers have joined.
                unsafe { drop(Box::from_raw(node.cache.get_ptr::<HashProcessingData<Idx>>())) };
                node.status.store(status::NOT_STARTED, Ordering::Relaxed);
            }
        });
    }
}
