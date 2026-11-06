//! State retained between executor runs while all workers are stopped.

use super::super::hashtable::Idx;

pub(in crate::quadtree) struct PausedWork<T> {
    pub(in crate::quadtree) roots: Vec<(Idx, u32)>,
    pub(super) tasks: Vec<T>,
    pub(super) root_finished: bool,
}

impl<T> PausedWork<T> {
    pub(in crate::quadtree) fn can_resume(&self) -> bool {
        self.root_finished || !self.tasks.is_empty()
    }
}
