//! # QuadTree Node Module
//!
//! This module defines the core data structures for the parallel Hashlife algorithm.
//!
//! ## Architecture Overview
//!
//! The parallel Hashlife uses a work-stealing approach where multiple threads
//! process nodes concurrently. Each node has a status that tracks its processing state.
//!
//! ## Status State Machine
//!
//! ```text
//!     ┌──────────────────────┐
//!     │    NOT_STARTED (0)   │ ◄── Initial state
//!     └──────────┬───────────┘
//!                │
//!                │ CAS(NOT_STARTED → PROCESSING)
//!                │ by first thread to claim this node
//!                ▼
//!     ┌──────────────────────┐                      ┌──────────────────────┐
//!     │    PROCESSING (1)    │ ◄─┐                  │    FINISHED (3)      │
//!     └──────────┬───────────┘   │                  └──────────────────────┘
//!                │               │                            ▲
//!                ├───────────────┼────────────────────────────┘
//!                │               │  store(FINISHED) when done
//!                │ store(PENDING)│
//!                │ when waiting  │ CAS(PENDING → PROCESSING)
//!                │ for deps      │ when dependency notifies us
//!                ▼               │
//!     ┌──────────────────────┐   │
//!     │     PENDING (2)      │ ──┘ Waiting for dependencies
//!     └──────────────────────┘
//! ```
//!
//! ## Thread Safety
//!
//! - `status` is `AtomicU8` - safe for concurrent access
//! - `cache` is protected by the status state machine:
//!   - Only the thread that successfully CAS'd to PROCESSING can write
//!   - Other threads must wait for FINISHED before reading the result

use smallvec::SmallVec;
use std::{
    cell::UnsafeCell,
    ptr,
    sync::atomic::{AtomicBool, AtomicU8},
};

/// Index of a node in the memory pool.
///
/// Each node has a unique `NodeIdx`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(super) struct NodeIdx(pub(super) u32);

/// List of nodes that depend on this node's result.
///
/// Uses `SmallVec` with inline capacity of 2 because:
/// - Most nodes have 0-2 dependents (parent nodes in the quadtree)
/// - Avoids heap allocation in the common case
/// - Falls back to heap for rare cases with more dependents
pub(super) type Dependents = SmallVec<[NodeIdx; 2]>;

/// Temporary data used while processing a node.
///
/// This struct is heap-allocated when processing starts and freed when
/// the node transitions to FINISHED. It's stored via pointer in `cache`.
#[derive(Default)]
pub(super) struct ProcessingData {
    /// Intermediate child results.
    /// - Indices 0-8: used for 9 overlapping children in stage 1
    /// - Indices 0-3: used for 4 children in stage 2
    pub(super) arr: [NodeIdx; 9],

    /// Bitmask tracking which of the 9 children are not yet ready.
    /// Bit i is set if `arr[i]` is still being computed.
    pub(super) mask9_waiting: u32,

    /// Bitmask tracking which of the 4 children are not yet ready.
    /// Bit i is set if `arr[i]` is still being computed.
    pub(super) mask4_waiting: u32,

    /// Number of dependencies we're waiting for.
    /// When this reaches 0, the node can be re-queued for processing.
    pub(super) waiting_cnt: u32,

    /// Nodes that depend on this node's result.
    /// When this node finishes, we decrement their `waiting_cnt`
    /// and re-queue them if they're ready.
    pub(super) dependents: Dependents,
}

/// Union type for the cache field.
///
/// This is a space optimization: we reuse the same memory for:
/// - A pointer to `ProcessingData` during computation
/// - The final `NodeIdx` result after computation
union PtrOrNodeIdx {
    /// Pointer to processing data
    ptr: *mut ProcessingData,
    /// Cached result node index
    node: NodeIdx,
}

impl Default for PtrOrNodeIdx {
    fn default() -> Self {
        PtrOrNodeIdx {
            ptr: ptr::null_mut(),
        }
    }
}

/// Thread-safe wrapper for `PtrOrNodeIdx`.
///
/// Uses `UnsafeCell` because the status state machine guarantees
/// that only one thread accesses this at a time:
/// - The thread holding PROCESSING status has exclusive access
/// - After FINISHED, the value is immutable
///
/// # Safety
///
/// Callers must ensure they only access this when they have the right
/// to do so according to the processing flow.
#[derive(Debug, Default)]
pub(super) struct PtrOrNodeIdxMut(UnsafeCell<PtrOrNodeIdx>);

impl PtrOrNodeIdxMut {
    pub(super) fn new() -> Self {
        PtrOrNodeIdxMut(UnsafeCell::new(PtrOrNodeIdx {
            ptr: std::ptr::null_mut(),
        }))
    }

    /// Get the cached result node index.
    pub(super) fn get_node_idx(&self) -> NodeIdx {
        unsafe { (*self.0.get()).node }
    }

    /// Set the cached result node index.
    pub(super) fn set_node_idx(&self, node: NodeIdx) {
        unsafe { (*self.0.get()).node = node }
    }

    /// Get a mutable reference to the processing data.
    pub(super) fn get_ref(&self) -> &mut ProcessingData {
        unsafe { &mut *(*self.0.get()).ptr }
    }

    /// Set the pointer to processing data.
    pub(super) fn set_ptr(&self, ptr: *mut ProcessingData) {
        unsafe { (*self.0.get()).ptr = ptr }
    }
}

/// A node of the quadtree.
///
/// # Structure
///
/// For internal nodes (non-leaf):
/// ```text
///     ┌────┬────┐
///     │ nw │ ne │
///     ├────┼────┤
///     │ sw │ se │
///     └────┴────┘
/// ```
///
/// For leaf nodes (8x8 cells):
/// - `nw` and `ne` together encode 64 cells as bits
/// - `sw` and `se` are unused
///
/// # Thread Safety
///
/// - `nw`, `ne`, `sw`, `se`: immutable after creation (no synchronization needed)
/// - `status`: `AtomicU8` for concurrent access
/// - `cache`: protected by status state machine
/// - `flags`: immutable after creation
/// - `lock_ht_slot`: `AtomicBool` for hashtable insertion synchronization
#[derive(Debug, Default)]
pub(super) struct QuadTreeNode<Extra> {
    // === Immutable after creation ===

    /// Northwest child (or lower 32 bits of leaf cells)
    pub(super) nw: NodeIdx,
    /// Northeast child (or upper 32 bits of leaf cells)
    pub(super) ne: NodeIdx,
    /// Southwest child
    pub(super) sw: NodeIdx,
    /// Southeast child
    pub(super) se: NodeIdx,

    // === Mutable, protected by status state machine ===

    /// Cache field with dual purpose:
    /// - During processing: pointer to `ProcessingData`
    /// - After computation completes: the computed result `NodeIdx`
    pub(super) cache: PtrOrNodeIdxMut,

    /// Processing status. See module docs for the state machine.
    ///
    /// Values: NOT_STARTED(0), PROCESSING(1), PENDING(2), FINISHED(3)
    pub(super) status: AtomicU8,

    // === Immutable after creation ===

    /// Flags encoding node properties:
    /// - Bit 0: is_leaf (1 = leaf node with cells, 0 = internal node)
    /// - Bit 1: is_used (1 = node is in use, 0 = node is free for reuse)
    pub(super) flags: u8,

    /// Lock for hashtable slot during concurrent insertions.
    ///
    /// When multiple threads try to insert the same node, this lock
    /// ensures only one succeeds and others find the existing node.
    pub(super) lock_ht_slot: AtomicBool,

    // === StreamLife extension (currently unused) ===

    /// Extra data for StreamLife algorithm.
    /// For Hashlife, this is `()` (zero-sized).
    pub(super) extra: UnsafeCell<Extra>,
}

// SAFETY: QuadTreeNode is Sync because:
// 1. Immutable fields (nw, ne, sw, se, flags) are safe to share
// 2. AtomicU8 (status) and AtomicBool (lock_ht_slot) are inherently Sync
// 3. cache (UnsafeCell) is protected by the status state machine
// 4. extra (UnsafeCell) is only accessed by StreamLife with proper synchronization
unsafe impl<Extra> Sync for QuadTreeNode<Extra> {}

impl<Extra> QuadTreeNode<Extra> {
    /// Check if this node slot is unused (available for allocation).
    pub(super) fn not_used(&self) -> bool {
        self.flags & 1 << 1 == 0
    }

    /// Build the flags byte from boolean properties.
    ///
    /// # Flag Layout
    /// ```text
    /// Bit 0: is_leaf  (1 = leaf with 8x8 cells, 0 = internal node)
    /// Bit 1: is_used  (1 = allocated, 0 = free slot)
    /// ```
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

    /// Compute hash for hashtable lookup.
    ///
    /// Uses a simple polynomial hash with prime-like multipliers.
    /// The final mixing step (h + h>>11) improves distribution.
    pub(super) fn hash(nw: NodeIdx, ne: NodeIdx, sw: NodeIdx, se: NodeIdx) -> usize {
        let h = 0u32
            .wrapping_add((nw.0).wrapping_mul(5))
            .wrapping_add((ne.0).wrapping_mul(17))
            .wrapping_add((sw.0).wrapping_mul(257))
            .wrapping_add((se.0).wrapping_mul(65537));
        h.wrapping_add(h >> 11) as usize
    }

    /// Get the four children as an array [nw, ne, sw, se].
    pub(super) fn parts(&self) -> [NodeIdx; 4] {
        [self.nw, self.ne, self.sw, self.se]
    }

    /// Returns the cells of a leaf node row by row (8 rows of 8 bits each).
    ///
    /// # Leaf Cell Layout
    ///
    /// For a leaf node, `nw` and `ne` together encode 64 cells:
    /// ```text
    /// nw (32 bits) = rows 0-3, columns 0-7
    /// ne (32 bits) = rows 4-7, columns 0-7
    ///
    /// Interpreted as [u8; 8]: each byte is one row
    /// ```
    pub(super) fn leaf_cells(&self) -> [u8; 8] {
        (self.nw.0 as u64 | ((self.ne.0 as u64) << 32)).to_le_bytes()
    }

    /// Extract the northwest 4x4 quadrant from an 8x8 leaf.
    ///
    /// # Layout
    /// ```text
    /// 8x8 leaf:           4x4 NW quadrant:
    /// ┌───────┬───────┐   ┌───────┐
    /// │ NW    │ NE    │   │ NW    │
    /// │ (4x4) │ (4x4) │   │ (4x4) │
    /// ├───────┼───────┤   └───────┘
    /// │ SW    │ SE    │
    /// │ (4x4) │ (4x4) │
    /// └───────┴───────┘
    /// ```
    ///
    /// Returns 16 bits representing a 4x4 grid (4 rows × 4 columns).
    pub(super) fn leaf_nw(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            // Extract lower 4 bits of each of the first 4 rows
            result |= ((self.nw.0 >> (i * 8)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Extract the northeast 4x4 quadrant from an 8x8 leaf.
    ///
    /// Returns 16 bits representing a 4x4 grid (4 rows × 4 columns).
    pub(super) fn leaf_ne(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            // Extract upper 4 bits of each of the first 4 rows
            result |= ((self.nw.0 >> (i * 8 + 4)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Extract the southwest 4x4 quadrant from an 8x8 leaf.
    ///
    /// Returns 16 bits representing a 4x4 grid (4 rows × 4 columns).
    pub(super) fn leaf_sw(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            // Extract lower 4 bits of each of the last 4 rows
            result |= ((self.ne.0 >> (i * 8)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Extract the southeast 4x4 quadrant from an 8x8 leaf.
    ///
    /// Returns 16 bits representing a 4x4 grid (4 rows × 4 columns).
    pub(super) fn leaf_se(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            // Extract upper 4 bits of each of the last 4 rows
            result |= ((self.ne.0 >> (i * 8 + 4)) & 0xF) << (i * 4);
        }
        result as u16
    }
}
