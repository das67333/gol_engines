use super::{
    LEAF_SIZE_LOG2,
    hashtable::{Idx, NodeStore},
};

pub(super) struct BlankNodes {
    data: Vec<Idx>,
}

impl BlankNodes {
    pub(super) fn new() -> Self {
        Self { data: vec![] }
    }

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

    pub(super) fn get(&self, size_log2: u32) -> Idx {
        let i = (size_log2 - LEAF_SIZE_LOG2) as usize;
        self.data[i]
    }

    pub(super) fn clear(&mut self) {
        self.data.clear();
    }
}
