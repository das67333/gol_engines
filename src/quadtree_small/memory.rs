use super::{ChunkVec, NodeIdx, QuadTreeNode, LEAF_SIZE_LOG2};

const CHUNK_SIZE: usize = 1 << 13;

/// Wrapper around MemoryManager::find_node that prefetches the node from the hashtable.
pub(super) struct PrefetchedNode<Extra> {
    kiv: *mut KIVMap<Extra>,
    nw: NodeIdx,
    ne: NodeIdx,
    sw: NodeIdx,
    se: NodeIdx,
    hash: usize,
}

/// Hashtable that stores nodes of the quadtree.
struct KIVMap<Extra> {
    // all allocated nodes
    storage: ChunkVec<CHUNK_SIZE, Extra>,
    // buffer where heads of linked lists are stored
    hashtable: Vec<NodeIdx>,
}

pub(super) struct MemoryManager<Extra> {
    layers: Vec<KIVMap<Extra>>,
}

impl<Extra: Clone + Default> PrefetchedNode<Extra> {
    pub(super) fn new(
        mem: &MemoryManager<Extra>,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        size_log2: u32,
    ) -> Self {
        let hash = QuadTreeNode::<Extra>::hash(nw, ne, sw, se);
        let kiv = unsafe {
            mem.layers
                .get_unchecked((size_log2 - LEAF_SIZE_LOG2) as usize)
        };

        #[cfg(target_arch = "x86_64")]
        unsafe {
            use std::arch::x86_64::*;
            let idx = hash & (kiv.hashtable.len() - 1);
            _mm_prefetch::<_MM_HINT_T0>(
                kiv.hashtable.get_unchecked(idx) as *const NodeIdx as *const i8
            );
        }

        Self {
            kiv: kiv as *const KIVMap<Extra> as *mut KIVMap<Extra>,
            nw,
            ne,
            sw,
            se,
            hash,
        }
    }

    pub(super) fn find_or_create(&self) -> NodeIdx {
        unsafe { (*self.kiv).find_or_create(self.nw, self.ne, self.sw, self.se, self.hash) }
    }
}

impl<Extra: Clone + Default> KIVMap<Extra> {
    fn new() -> Self {
        assert!(CHUNK_SIZE.is_power_of_two());
        assert!(u32::try_from(CHUNK_SIZE).is_ok(), "u32 is insufficient");
        // reserving NodeIdx(0) for blank node
        Self {
            storage: ChunkVec::new(),
            hashtable: vec![NodeIdx(0); CHUNK_SIZE],
        }
    }

    unsafe fn rehash(&mut self) {
        let new_size = self.hashtable.len() << 1;
        assert!(u32::try_from(new_size).is_ok(), "u32 is insufficient");
        let mut new_buf = vec![NodeIdx(0); new_size];
        for mut node in std::mem::take(&mut self.hashtable) {
            while node != NodeIdx(0) {
                let n = &self.storage[node];
                let hash = QuadTreeNode::<Extra>::hash(n.nw, n.ne, n.sw, n.se);
                let next = n.next;
                let index = hash & (new_size - 1);
                self.storage[node].next = *new_buf.get_unchecked(index);
                *new_buf.get_unchecked_mut(index) = node;
                node = next;
            }
        }
        self.hashtable = new_buf;
    }

    fn invalidate_cache(&mut self) {
        for i in 1..self.storage.len() {
            self.storage[NodeIdx(i as u32)].has_cache = false;
        }
    }

    /// Find an item in hashtable; if it is not present, it is created.
    /// Returns its index in hashtable.
    unsafe fn find_or_create(
        &mut self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        hash: usize,
    ) -> NodeIdx {
        if nw == NodeIdx(0) && ne == NodeIdx(0) && sw == NodeIdx(0) && se == NodeIdx(0) {
            return NodeIdx(0);
        }

        let i = hash & (self.hashtable.len() - 1);
        let mut node = *self.hashtable.get_unchecked(i);
        let mut prev = NodeIdx(0);
        // search for the node in the linked list
        while node != NodeIdx(0) {
            let n = &self.storage[node];
            if n.nw == nw && n.ne == ne && n.sw == sw && n.se == se {
                // move the node to the front of the list
                if prev != NodeIdx(0) {
                    self.storage[prev].next = n.next;
                    self.storage[node].next = *self.hashtable.get_unchecked(i);
                    *self.hashtable.get_unchecked_mut(i) = node;
                }
                return node;
            }
            prev = node;
            node = n.next;
        }

        let idx = self.storage.allocate();
        self.storage[idx] = QuadTreeNode {
            nw,
            ne,
            sw,
            se,
            next: *self.hashtable.get_unchecked(i),
            ..Default::default()
        };
        *self.hashtable.get_unchecked_mut(i) = idx;
        // double the number of buckets if the load factor is higher than 0.5
        if self.storage.len() * 2 > self.hashtable.len() {
            self.rehash();
        }
        idx
    }

    fn filter_unmarked_from_hashtable(&mut self) {
        for idx in self.hashtable.iter_mut() {
            let (mut curr, mut marked) = (*idx, NodeIdx(0));
            while curr != NodeIdx(0) {
                let next = self.storage[curr].next;
                if self.storage[curr].gc_marked {
                    self.storage[curr].next = marked;
                    marked = curr;
                }
                curr = next;
            }

            *idx = marked;
        }
    }

    fn gc_finish(&mut self) {
        self.filter_unmarked_from_hashtable();
        self.storage.deallocate_unmarked_and_unmark();
    }

    fn bytes_total(&self) -> usize {
        self.storage.bytes_total() + self.hashtable.capacity() * std::mem::size_of::<NodeIdx>()
    }

    fn len(&self) -> usize {
        self.storage.len()
    }

    fn capacity(&self) -> usize {
        self.storage.capacity()
    }
}

impl<Extra: Clone + Default> MemoryManager<Extra> {
    /// Create a new memory manager.
    pub(super) fn new() -> Self {
        Self {
            layers: vec![KIVMap::new()],
        }
    }

    /// Get a const reference to the node at the given index.
    #[inline]
    pub(super) fn get(&self, idx: NodeIdx, size_log2: u32) -> &QuadTreeNode<Extra> {
        let i = (size_log2 - LEAF_SIZE_LOG2) as usize;
        debug_assert!(self.layers.len() > i && self.layers[i].capacity() > idx.0 as usize);
        unsafe { &self.layers.get_unchecked(i).storage[idx] }
    }

    /// Get a mutable reference to the node at the given index.
    #[inline]
    pub(super) fn get_mut(&mut self, idx: NodeIdx, size_log2: u32) -> &mut QuadTreeNode<Extra> {
        let i = (size_log2 - LEAF_SIZE_LOG2) as usize;
        debug_assert!(self.layers.len() > i && self.layers[i].capacity() > idx.0 as usize);
        unsafe { &mut self.layers.get_unchecked_mut(i).storage[idx] }
    }

    pub(super) fn invalidate_cache(&mut self, since_size_log2: u32) {
        let lower = (since_size_log2 - LEAF_SIZE_LOG2) as usize;
        for i in lower..self.layers.len() {
            self.layers[i].invalidate_cache();
        }
    }

    /// Find a leaf node with the given parts.
    /// If the node is not found, it is created.
    ///
    /// `nw`, `ne`, `sw`, `se` are 16-bit integers, where each 4 bits represent a row of 4 cells.
    pub(super) fn find_or_create_leaf_from_parts(
        &mut self,
        nw: u16,
        ne: u16,
        sw: u16,
        se: u16,
    ) -> NodeIdx {
        let [mut nw, mut ne, mut sw, mut se] = [nw as u64, ne as u64, sw as u64, se as u64];
        let mut cells = 0;
        let mut shift = 0;
        for _ in 0..4 {
            cells |= (nw & 0xF) << shift;
            nw >>= 4;
            shift += 4;
            cells |= (ne & 0xF) << shift;
            ne >>= 4;
            shift += 4;
        }
        for _ in 0..4 {
            cells |= (sw & 0xF) << shift;
            sw >>= 4;
            shift += 4;
            cells |= (se & 0xF) << shift;
            se >>= 4;
            shift += 4;
        }
        self.find_or_create_leaf_from_u64(cells)
    }

    /// Find a leaf node with the given cells.
    /// If the node is not found, it is created.
    ///
    /// `cells` is u64 built by concatenating rows of cells.
    pub(super) fn find_or_create_leaf_from_u64(&mut self, cells: u64) -> NodeIdx {
        let nw = NodeIdx(cells as u32);
        let ne = NodeIdx((cells >> 32) as u32);
        let [sw, se] = [NodeIdx(0); 2];
        let hash = QuadTreeNode::<Extra>::hash(nw, ne, sw, se);
        unsafe {
            self.layers
                .get_unchecked_mut(0)
                .find_or_create(nw, ne, sw, se, hash)
        }
    }

    /// Find a node with the given parts.
    ///
    /// `size_log2` is related to the result! `nw`, `ne`, `sw`, `se` are `size_log2 - 1`
    ///
    /// If the node is not found, it is created.
    pub(super) fn find_or_create_node(
        &mut self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        size_log2: u32,
    ) -> NodeIdx {
        let i = (size_log2 - LEAF_SIZE_LOG2) as usize;
        let hash = QuadTreeNode::<Extra>::hash(nw, ne, sw, se);
        if self.layers.len() <= i {
            self.layers.resize_with(i + 1, KIVMap::new);
        }
        unsafe {
            self.layers
                .get_unchecked_mut(i)
                .find_or_create(nw, ne, sw, se, hash)
        }
    }

    pub(super) fn gc_finish(&mut self) {
        for kiv in self.layers.iter_mut() {
            kiv.gc_finish();
        }
    }

    pub(super) fn bytes_total(&self) -> usize {
        self.layers.iter().map(|m| m.bytes_total()).sum::<usize>()
    }

    #[allow(dead_code)]
    pub(super) fn stats_fast(&self) -> String {
        let mut s = String::new();

        s += &format!(
            "Memory spent on kivtables: {} MB\n",
            self.bytes_total() >> 20,
        );

        let nodes_total = self.layers.iter().map(|m| m.len()).sum::<usize>();
        s += "Nodes' sizes (side lengths) distribution:\n";
        s += &format!("total - {}\n", nodes_total);
        for (i, m) in self.layers.iter().enumerate() {
            let percent = m.len() * 100 / nodes_total;
            if percent == 0 {
                continue;
            }
            s += &format!("2^{:<2} -{:>3}%\n", LEAF_SIZE_LOG2 + i as u32, percent,);
        }
        s
    }
}
