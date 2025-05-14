/// Location of a node is determined by its `idx`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(super) struct NodeIdx(pub(super) u32);

/// A node of the quadtree.
///
/// If the node is a leaf, `nw` and `ne` are the data.
#[derive(Clone, Debug, Default)]
pub(super) struct QuadTreeNode<Extra> {
    pub(super) nw: NodeIdx,
    pub(super) ne: NodeIdx,
    pub(super) sw: NodeIdx,
    pub(super) se: NodeIdx,
    /// valid only if `has_cache` is true
    pub(super) cache: NodeIdx,
    pub(super) has_cache: bool,
    pub(super) is_leaf: bool,
    pub(super) is_used: bool,
    /// extra information for engine: () for hashlife and u64 for streamlife
    pub(super) extra: Extra,
}

impl<Extra> QuadTreeNode<Extra> {
    // pub(super) fn is_leaf(&self) -> bool {
    //     self.ctrl >> 6 == 1
    // }

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
