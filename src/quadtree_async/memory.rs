use super::{
    node::{NodeIdx, QuadTreeNode},
    statistics::ExecutionStatistics,
};
use std::{cell::UnsafeCell, hint, sync::atomic::Ordering};

/// Stores the nodes of the quadtree.
pub(super) struct MemoryManager<Extra> {
    base: UnsafeCell<MemoryManagerRaw<Extra>>,
}

unsafe impl<Extra: Sync> Sync for MemoryManager<Extra> {}

impl<Extra: Default> MemoryManager<Extra> {
    /// Create a new memory manager with a capacity of `1 << cap_log2`.
    pub(super) fn with_capacity(cap_log2: u32) -> Self {
        Self {
            base: UnsafeCell::new(MemoryManagerRaw::with_capacity(cap_log2)),
        }
    }

    /// Get a const reference to the node at the given index.
    pub(super) fn get(&self, idx: NodeIdx) -> &QuadTreeNode<Extra> {
        unsafe { (*self.base.get()).get(idx) }
    }

    /// Find a leaf node with the given parts.
    /// If the node is not found, it is created.
    ///
    /// `nw`, `ne`, `sw`, `se` are 16-bit integers, where each 4 bits represent a row of 4 cells.
    pub(super) fn find_or_create_leaf_from_parts(
        &self,
        nw: u16,
        ne: u16,
        sw: u16,
        se: u16,
    ) -> NodeIdx {
        /// See Morton order: https://en.wikipedia.org/wiki/Z-order_curve
        fn demorton_u64(nw: u16, ne: u16, sw: u16, se: u16) -> u64 {
            let (mut nw, mut ne, mut sw, mut se) = (nw as u64, ne as u64, sw as u64, se as u64);
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
            cells
        }

        let cells = demorton_u64(nw, ne, sw, se).to_le_bytes();
        self.find_or_create_leaf_from_array(cells)
    }

    pub(super) fn find_or_create_leaf_from_u64(&self, value: u64) -> NodeIdx {
        self.find_or_create_leaf_from_array(value.to_le_bytes())
    }

    /// Find a leaf node with the given cells.
    /// If the node is not found, it is created.
    ///
    /// `cells` is an array of 8 bytes, where each byte represents a row of 8 cells.
    pub(super) fn find_or_create_leaf_from_array(&self, cells: [u8; 8]) -> NodeIdx {
        let nw = NodeIdx(u32::from_le_bytes(cells[0..4].try_into().unwrap()));
        let ne = NodeIdx(u32::from_le_bytes(cells[4..8].try_into().unwrap()));
        let [sw, se] = [NodeIdx::default(); 2];
        let hash = QuadTreeNode::<Extra>::hash(nw, ne, sw, se);
        unsafe { (*self.base.get()).find_or_create_inner(nw, ne, sw, se, hash, true) }
    }

    /// Find a node with the given parts.
    /// If the node is not found, it is created.
    pub(super) fn find_or_create_node(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
    ) -> NodeIdx {
        let hash = QuadTreeNode::<Extra>::hash(nw, ne, sw, se);
        unsafe { (*self.base.get()).find_or_create_inner(nw, ne, sw, se, hash, false) }
    }

    pub(super) fn clear(&mut self) {
        self.base
            .get_mut()
            .hashtable
            .fill_with(QuadTreeNode::default);
    }

    pub(super) fn bytes_total(&self) -> usize {
        unsafe { (*self.base.get()).bytes_total() }
    }
}

/// Hashtable that stores nodes of the quadtree
struct MemoryManagerRaw<Extra> {
    /// buffer where heads of linked lists are stored
    hashtable: Vec<QuadTreeNode<Extra>>,
}

impl<Extra: Default> MemoryManagerRaw<Extra> {
    /// Create a new memory manager with a capacity of `1 << cap_log2`.
    fn with_capacity(cap_log2: u32) -> Self {
        assert!(
            cap_log2 <= 32,
            "Hashtables bigger than 2^32 are not supported"
        );
        Self {
            hashtable: (0..1u64 << cap_log2)
                .map(|_| QuadTreeNode::default())
                .collect(),
        }
    }

    /// Get a const reference to the node at the given index.
    #[inline]
    fn get(&self, idx: NodeIdx) -> &QuadTreeNode<Extra> {
        unsafe { self.hashtable.get_unchecked(idx.0 as usize) }
    }

    /// Find an item in hashtable; if it is not present, it is created and its index in hashtable is returned.
    unsafe fn find_or_create_inner(
        &mut self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        hash: usize,
        is_leaf: bool,
    ) -> NodeIdx {
        if ExecutionStatistics::is_poisoned() {
            return NodeIdx::default();
        }

        let mask = self.hashtable.len() - 1;
        let mut index = hash & mask;
        let flags = QuadTreeNode::<Extra>::build_flags(is_leaf, true);

        loop {
            // First check if we can acquire the lock for this index
            let lock = &(*self.hashtable.as_mut_ptr().add(index)).lock_ht_slot;

            while lock
                .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_err()
            {
                while lock.load(Ordering::Relaxed) {
                    hint::spin_loop();
                }
            }

            // Now safely get the mutable reference after acquiring the lock
            let n = self.hashtable.get_unchecked_mut(index);

            if n.nw == nw && n.ne == ne && n.sw == sw && n.se == se && n.flags == flags {
                lock.store(false, Ordering::Release);
                break;
            }

            if n.not_used() {
                n.nw = nw;
                n.ne = ne;
                n.sw = sw;
                n.se = se;
                n.flags = flags;
                lock.store(false, Ordering::Release);

                ExecutionStatistics::on_insertion::<0>();
                // NODES_CREATED_COUNT.fetch_add(1, Ordering::Relaxed);
                break;
            }

            lock.store(false, Ordering::Release);
            index = index.wrapping_add(1) & mask;
        }

        NodeIdx(index as u32)
    }

    fn bytes_total(&self) -> usize {
        self.hashtable.capacity() * std::mem::size_of::<QuadTreeNode<Extra>>()
    }
}
