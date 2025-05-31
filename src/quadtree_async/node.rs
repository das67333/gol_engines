use std::{
    cell::UnsafeCell,
    sync::atomic::{AtomicBool, AtomicU8},
};

/// Location of a node is determined by its `idx`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(super) struct NodeIdx(pub(super) u32);

/// A node of the quadtree.
///
/// If the node is a leaf, `nw` and `ne` are the data.
#[derive(Debug, Default)]
pub(super) struct QuadTreeNode<Extra> {
    pub(super) nw: NodeIdx,
    pub(super) ne: NodeIdx,
    pub(super) sw: NodeIdx,
    pub(super) se: NodeIdx,
    /// valid only if `status` is `STATUS_CACHED`
    pub(super) cache: UnsafeCell<NodeIdx>,
    pub(super) status: AtomicU8,
    pub(super) flags: u8,
    pub(super) lock: AtomicBool,
    pub(super) status_extra: AtomicU8,   // status for extra
    pub(super) extra: UnsafeCell<Extra>, // extra information for engine: () for hashlife and u64 for streamlife
}

unsafe impl<Extra> Sync for QuadTreeNode<Extra> {}

impl<Extra> QuadTreeNode<Extra> {
    pub(super) fn not_used(&self) -> bool {
        self.flags & 1 << 1 == 0
    }

    pub(super) fn build_flags(is_leaf: bool, is_used: bool) -> u8 {
        let mut flags = 0;
        if is_leaf {
            flags |= 1 << 0;
        }
        if is_used {
            flags |= 1 << 1;
        }
        flags
    }

    pub(super) fn hash(nw: NodeIdx, ne: NodeIdx, sw: NodeIdx, se: NodeIdx) -> usize {
        let h = 0u32
            .wrapping_add((nw.0).wrapping_mul(5))
            .wrapping_add((ne.0).wrapping_mul(17))
            .wrapping_add((sw.0).wrapping_mul(257))
            .wrapping_add((se.0).wrapping_mul(65537));
        h.wrapping_add(h >> 11) as usize
    }

    pub(super) fn parts(&self) -> [NodeIdx; 4] {
        [self.nw, self.ne, self.sw, self.se]
    }

    /// Returns the cells of a leaf node row by row.
    pub(super) fn leaf_cells(&self) -> [u8; 8] {
        (self.nw.0 as u64 | ((self.ne.0 as u64) << 32)).to_le_bytes()
    }

    pub(super) fn leaf_nw(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.nw.0 >> (i * 8)) & 0xF) << (i * 4);
        }
        result as u16
    }

    pub(super) fn leaf_ne(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.nw.0 >> (i * 8 + 4)) & 0xF) << (i * 4);
        }
        result as u16
    }

    pub(super) fn leaf_sw(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.ne.0 >> (i * 8)) & 0xF) << (i * 4);
        }
        result as u16
    }

    pub(super) fn leaf_se(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.ne.0 >> (i * 8 + 4)) & 0xF) << (i * 4);
        }
        result as u16
    }
}
