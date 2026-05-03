use super::{
    LEAF_SIZE_LOG2,
    hashtable::{Idx, NodeStore},
};

/// Lazily-extended chain of all-zero nodes, one per tree level.
///
/// `data[0]` is the blank 8×8 leaf (`size_log2 == LEAF_SIZE_LOG2`).
/// `data[i]` is a node at level `LEAF_SIZE_LOG2 + i` whose four children
/// are all `data[i-1]`. Entries are created on demand by [`Self::get_mut`]
/// and retrieved cheaply (without allocation) by [`Self::get`].
pub(super) struct BlankNodes {
    data: Vec<Idx>,
}

impl BlankNodes {
    pub(super) fn new() -> Self {
        Self { data: vec![] }
    }

    /// Return the blank node at the given level, extending the chain if needed.
    pub(super) fn get_mut<Meta: Default + Sync>(
        &mut self,
        size_log2: u32,
        mem: &NodeStore<Meta>,
    ) -> Idx {
        let i = (size_log2 - LEAF_SIZE_LOG2) as usize;
        let v = &mut self.data;
        while v.len() <= i {
            if let Some(&b) = v.last() {
                v.push(mem.find_or_create_node(b, b, b, b));
            } else {
                v.push(mem.find_or_create_leaf_from_u64(0));
            };
        }
        v[i]
    }

    /// Return the blank node at the given level. Panics if not yet populated.
    pub(super) fn get(&self, size_log2: u32) -> Idx {
        let i = (size_log2 - LEAF_SIZE_LOG2) as usize;
        self.data[i]
    }

    pub(super) fn clear(&mut self) {
        self.data.clear();
    }
}
