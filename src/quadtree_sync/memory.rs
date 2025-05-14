use super::{NodeIdx, QuadTreeNode, LEAF_SIZE_LOG2};
use std::cell::UnsafeCell;

/// Wrapper around MemoryManager::find_or_create_node that prefetches the node from the hashtable.
pub(super) struct PrefetchedNode<Extra> {
    mem: *mut MemoryManager<Extra>,
    nw: NodeIdx,
    ne: NodeIdx,
    sw: NodeIdx,
    se: NodeIdx,
    is_leaf: bool,
    hash: usize,
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

        #[cfg(target_arch = "x86_64")]
        unsafe {
            use std::arch::x86_64::*;
            let idx = hash & ((*mem.base.get()).hashtable.len() - 1);
            _mm_prefetch::<_MM_HINT_T0>((*mem.base.get()).hashtable.get_unchecked(idx)
                as *const QuadTreeNode<Extra> as *const i8);
        }
        Self {
            mem: mem as *const MemoryManager<Extra> as *mut MemoryManager<Extra>,
            nw,
            ne,
            sw,
            se,
            is_leaf: size_log2 == LEAF_SIZE_LOG2,
            hash,
        }
    }

    pub(super) fn find_or_create(&self) -> NodeIdx {
        unsafe {
            (*(*self.mem).base.get()).find_or_create_inner(
                self.nw,
                self.ne,
                self.sw,
                self.se,
                self.hash,
                self.is_leaf,
            )
        }
    }
}

pub(super) struct MemoryManager<Extra> {
    base: UnsafeCell<MemoryManagerRaw<Extra>>,
}

impl<Extra: Clone + Default> MemoryManager<Extra> {
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

    /// Get a mutable reference to the node at the given index.
    pub(super) fn get_mut(&self, idx: NodeIdx) -> &mut QuadTreeNode<Extra> {
        unsafe { (*self.base.get()).get_mut(idx) }
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
        self.base.get_mut().len = 0;
        self.base.get_mut().poisoned = false;
    }

    pub(super) fn bytes_total(&self) -> usize {
        unsafe { (*self.base.get()).bytes_total() }
    }

    pub(super) fn poisoned(&self) -> bool {
        unsafe { (*self.base.get()).poisoned }
    }
}

/// Hashtable that stores nodes of the quadtree
struct MemoryManagerRaw<Extra> {
    /// buffer where heads of linked lists are stored
    hashtable: Vec<QuadTreeNode<Extra>>,
    /// number of nodes that were created
    len: usize,
    /// if true, the hashtable is poisoned and should be restored from the backup
    poisoned: bool,
}

impl<Extra: Clone + Default> MemoryManagerRaw<Extra> {
    /// Create a new memory manager with a capacity of `1 << cap_log2`.
    fn with_capacity(cap_log2: u32) -> Self {
        assert!(
            cap_log2 <= 32,
            "Hashtables bigger than 2^32 are not supported"
        );
        Self {
            hashtable: (0..1u64 << cap_log2)
                .map(|_| QuadTreeNode::<Extra>::default())
                .collect(),
            len: 0,
            poisoned: false,
        }
    }

    /// Get a const reference to the node at the given index.
    #[inline]
    fn get(&self, idx: NodeIdx) -> &QuadTreeNode<Extra> {
        unsafe { self.hashtable.get_unchecked(idx.0 as usize) }
    }

    /// Get a mutable reference to the node at the given index.
    #[inline]
    fn get_mut(&mut self, idx: NodeIdx) -> &mut QuadTreeNode<Extra> {
        unsafe { self.hashtable.get_unchecked_mut(idx.0 as usize) }
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
        if self.poisoned {
            return NodeIdx::default();
        }

        let mask = self.hashtable.len() - 1;
        let mut index = hash & mask;

        loop {
            let n = self.hashtable.get_unchecked(index);
            if n.nw == nw
                && n.ne == ne
                && n.sw == sw
                && n.se == se
                && n.is_leaf == is_leaf
                && n.is_used
            {
                break;
            }

            if !n.is_used {
                *self.hashtable.get_unchecked_mut(index) = QuadTreeNode {
                    nw,
                    ne,
                    sw,
                    se,
                    is_leaf,
                    is_used: true,
                    ..Default::default()
                };
                self.len += 1;
                if self.len > self.hashtable.len() * 3 / 4 {
                    self.poisoned = true;
                    return NodeIdx::default();
                }
                break;
            }

            index = index.wrapping_add(1) & mask;
        }

        NodeIdx(index as u32)
    }

    fn bytes_total(&self) -> usize {
        self.hashtable.len() * std::mem::size_of::<QuadTreeNode<Extra>>()
    }
}
