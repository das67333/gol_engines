//! # QuadTree Node Data Structures
//!
//! Core data structures for representing nodes in the parallel Hashlife quadtree.
//!
//! ## Node Structure
//!
//! Each [`QuadTreeNode`] represents either:
//! - **Internal node**: 4 children (nw, ne, sw, se) forming a 2×2 block
//! - **Leaf node**: 8×8 grid of cells encoded in `nw` and `ne` fields
//!
//! ## Processing State
//!
//! Nodes track their computation state via the `status` field.
//! See `hashlife_executor` module for the complete state machine diagram.
//!
//! ## Cache Field
//!
//! The `cache` field is a union that serves dual purposes:
//! - During processing: pointer to [`ProcessingData`]
//! - After completion: cached result [`NodeIdx`]
//!
//! This space optimization reuses the same memory for both purposes.

use smallvec::SmallVec;
use std::{cell::UnsafeCell, ptr, sync::atomic::AtomicU8};

/// Index uniquely identifying a node in the memory manager.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(super) struct NodeIdx(pub(super) u32);

/// List of nodes waiting for this node's result.
///
/// Optimized with `SmallVec<[_; 2]>` to avoid heap allocation in the common case,
/// since almost every node (>>99.99%) has 1 dependent. A capacity of 2 is used
/// because it does not increase the struct size compared to a capacity of 1.
pub(super) type Dependents = SmallVec<[NodeIdx; 2]>;

/// Temporary data allocated during node processing.
///
/// Heap-allocated when processing starts, freed when node reaches FINISHED state.
/// Stored via pointer in the node's `cache` field.
#[derive(Default)]
pub(super) struct ProcessingData {
    /// Intermediate child node results (up to 9 for overlapping, 4 for final stage).
    pub(super) arr: [NodeIdx; 9],
    /// Bitmask: bit `i` set if `arr[i]` (among first 9) is not yet computed.
    pub(super) mask9_waiting: u32,
    /// Bitmask: bit `i` set if `arr[i]` (among first 4) is not yet computed.
    pub(super) mask4_waiting: u32,
    /// Count of dependencies still being computed. Node can resume when this reaches 0.
    pub(super) waiting_cnt: u32,
    /// Nodes that registered as dependents of this node.
    /// Notified when this node finishes.
    pub(super) dependents: Dependents,
}

/// Union for cache field: either processing data pointer or result node.
///
/// Space optimization that reuses the same memory for both purposes.
/// The active variant depends on the node's processing state.
union PtrOrNodeIdx {
    ptr: *mut ProcessingData,
    node: NodeIdx,
}

impl Default for PtrOrNodeIdx {
    fn default() -> Self {
        PtrOrNodeIdx {
            ptr: ptr::null_mut(),
        }
    }
}

/// Thread-safe wrapper for the cache union.
///
/// Safety is guaranteed by the status state machine:
/// only the thread holding PROCESSING status can mutate this.
#[derive(Debug, Default)]
pub(super) struct PtrOrNodeIdxMut(UnsafeCell<PtrOrNodeIdx>);

impl PtrOrNodeIdxMut {
    pub(super) fn get_node_idx(&self) -> NodeIdx {
        unsafe { (*self.0.get()).node }
    }

    pub(super) fn set_node_idx(&self, node: NodeIdx) {
        unsafe { (*self.0.get()).node = node }
    }

    pub(super) fn get_ref(&self) -> &mut ProcessingData {
        unsafe { &mut *(*self.0.get()).ptr }
    }

    pub(super) fn set_ptr(&self, ptr: *mut ProcessingData) {
        unsafe { (*self.0.get()).ptr = ptr }
    }
}

/// A node in the Hashlife quadtree.
///
/// ## Structure
///
/// **Internal nodes** (non-leaf):
/// ```text
///     ┌────┬────┐
///     │ nw │ ne │
///     ├────┼────┤
///     │ sw │ se │
///     └────┴────┘
/// ```
///
/// **Leaf nodes** (8×8 cells):
/// - `nw` and `ne` encode 64 cells as bits (32 bits each)
/// - `sw` and `se` are unused
///
/// ## Thread Safety
///
/// DO NOT CREATE A MUTABLE REFERENCE AFTER CREATION!
/// - `nw`, `ne`, `sw`, `se`: immutable after creation
/// - `cache`: protected by status state machine, wraps [`UnsafeCell`]
/// - `status`: atomic for concurrent state transitions
/// - `flags`: atomic, combines node metadata and hashtable slot lock
#[derive(Debug, Default)]
pub(super) struct QuadTreeNode<Extra> {
    /// Northwest child or lower 32 bits of leaf cells
    pub(super) nw: NodeIdx,
    /// Northeast child or upper 32 bits of leaf cells
    pub(super) ne: NodeIdx,
    /// Southwest child (unused for leaves)
    pub(super) sw: NodeIdx,
    /// Southeast child (unused for leaves)
    pub(super) se: NodeIdx,
    /// Cache: either ProcessingData pointer or result NodeIdx
    pub(super) cache: PtrOrNodeIdxMut,
    /// Processing status (see hashlife_executor for state machine)
    pub(super) status: AtomicU8,
    /// Flags are used in [`MemoryManager::find_or_create_inner`]
    pub(super) flags: AtomicU8,
    /// Extra data for StreamLife (unused in Hashlife)
    pub(super) extra: UnsafeCell<Extra>,
    pub(super) status_extra: AtomicU8,
}

// SAFETY: Sync because atomics handle synchronization and cache is protected by status state machine
unsafe impl<Extra> Sync for QuadTreeNode<Extra> {}

impl<Extra> QuadTreeNode<Extra> {
    /// Return children as array [nw, ne, sw, se].
    pub(super) fn parts(&self) -> [NodeIdx; 4] {
        [self.nw, self.ne, self.sw, self.se]
    }

    /// Extract leaf cells as 8 bytes (one byte per row).
    ///
    /// Layout: `nw` = rows 0-3, `ne` = rows 4-7
    pub(super) fn leaf_cells(&self) -> [u8; 8] {
        (self.nw.0 as u64 | ((self.ne.0 as u64) << 32)).to_le_bytes()
    }

    /// Extract northwest 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_nw(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.nw.0 >> (i * 8)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Extract northeast 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_ne(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.nw.0 >> (i * 8 + 4)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Extract southwest 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_sw(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.ne.0 >> (i * 8)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Extract southeast 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_se(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.ne.0 >> (i * 8 + 4)) & 0xF) << (i * 4);
        }
        result as u16
    }
}
