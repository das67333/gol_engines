use super::{MemoryManager, NodeIdx, LEAF_SIZE_LOG2};

pub(super) struct BlankNodes {
    data: Vec<NodeIdx>,
}

impl BlankNodes {
    pub(super) fn new() -> Self {
        Self { data: vec![] }
    }

    pub(super) fn get<Extra: Default>(
        &mut self,
        size_log2: u32,
        mem: &MemoryManager<Extra>,
    ) -> NodeIdx {
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

    pub(super) fn clear(&mut self) {
        self.data.clear();
    }
}
