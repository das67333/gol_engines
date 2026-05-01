//! # QuadTree Node Data Structures
//!
//! Core data structures for representing nodes in the parallel Hashlife quadtree.
//!
//! ## Node Structure
//!
//! Each [`QuadTreeNode`] represents either:
//! - **Internal node**: 4 children (nw, ne, sw, se) forming a 2×2 block.
//! - **Leaf node**: 8×8 grid of cells encoded in `nw` and `ne` fields;
//!   `sw` and `se` are zero (the leaf marker — see [`Self::is_leaf`]).
//!
//! ## Processing State
//!
//! Nodes track their computation state via the `status` field.
//! See `hashlife_executor` module for the complete state machine diagram.
//!
//! ## Cache Field
//!
//! The `cache` field is a [`CacheField`] that serves dual purposes:
//! - During processing: type-erased pointer to processing data (defined in executor modules).
//! - After completion: cached result [`Idx`].
//!
//! ## Hashtable chain link
//!
//! The `next` field is the chain pointer for the chained
//! [`super::hashtable::ConcurrentHashTable`]. It also doubles as the
//! free-list link when the node is on a thread-local free list.

use super::hashtable::{CacheField, HashtableSlot, Idx};
use std::{
    cell::UnsafeCell,
    sync::atomic::{AtomicU8, AtomicU32},
};

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
/// - `sw` and `se` are both zero — this distinguishes leaves from internal
///   nodes, which always have non-null children (Idx 0 = null).
///
/// ## Field order
///
/// Carefully arranged to keep `QuadTreeNode<()>` (HashLife) at exactly 32 B
/// and `QuadTreeNode<u64>` (StreamLife) at 40 B; see the static asserts at
/// the end of this module.
///
/// ## Thread Safety
///
/// DO NOT CREATE A MUTABLE REFERENCE AFTER PUBLICATION!
/// - `nw`, `ne`, `sw`, `se`: written by the inserting thread before the
///   publishing CAS on the bucket head; immutable thereafter.
/// - `cache`: protected by the `status` state machine, wraps [`UnsafeCell`].
/// - `next`: atomic; chain pointer when in hashtable, free-list link when
///   freed.
/// - `status`: atomic bit-set encoding the async state machine
///   (see `super::status`).
/// - `extra`/`status_extra`: StreamLife lane descriptor + status; unused
///   for HashLife (`Meta = ()`).
#[derive(Default)]
pub(super) struct QuadTreeNode<Meta> {
    /// Northwest child or lower 32 bits of leaf cells.
    pub(super) nw: Idx,
    /// Northeast child or upper 32 bits of leaf cells.
    pub(super) ne: Idx,
    /// Southwest child; **zero on leaves** (leaf marker).
    pub(super) sw: Idx,
    /// Southeast child; **zero on leaves** (leaf marker).
    pub(super) se: Idx,
    /// Cache: either processing data pointer or result Idx.
    pub(super) cache: CacheField<Idx>,
    /// Chain pointer for the hashtable bucket; doubles as free-list link.
    pub(super) next: AtomicU32,
    /// Processing status (see hashlife_executor for state machine).
    pub(super) status: AtomicU8,
    /// Lane-descriptor status (StreamLife only).
    pub(super) status_extra: AtomicU8,
    /// Lane descriptor metadata (StreamLife only; zero-sized for HashLife).
    pub(super) extra: UnsafeCell<Meta>,
}

// SAFETY: Sync because atomics handle synchronization and `cache` is
// protected by the status state machine; `next` is atomic for chain walks;
// body fields are only mutated before publication via a Release-CAS on
// the bucket head.
unsafe impl<Meta> Sync for QuadTreeNode<Meta> {}

impl<Meta: Default + Sync> HashtableSlot for QuadTreeNode<Meta> {
    fn next(&self) -> &AtomicU32 {
        &self.next
    }
}

impl<Meta> QuadTreeNode<Meta> {
    /// Return children as array [nw, ne, sw, se].
    pub(super) fn parts(&self) -> [Idx; 4] {
        [self.nw, self.ne, self.sw, self.se]
    }

    /// True if this node is a leaf. Leaves have `sw == 0 && se == 0`;
    /// internal nodes always have non-null children (Idx 0 is null).
    #[allow(dead_code)]
    pub(super) fn is_leaf(&self) -> bool {
        self.sw == 0
    }

    /// Extract leaf cells as 8 bytes (one byte per row).
    ///
    /// Layout: `nw` = rows 0-3, `ne` = rows 4-7.
    pub(super) fn leaf_cells(&self) -> [u8; 8] {
        (self.nw as u64 | ((self.ne as u64) << 32)).to_le_bytes()
    }

    /// Extract northwest 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_nw(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.nw >> (i * 8)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Extract northeast 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_ne(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.nw >> (i * 8 + 4)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Extract southwest 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_sw(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.ne >> (i * 8)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Extract southeast 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_se(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.ne >> (i * 8 + 4)) & 0xF) << (i * 4);
        }
        result as u16
    }
}

// Compile-time size guarantees (see field-order rationale in struct doc).
const _: () = {
    assert!(
        std::mem::size_of::<QuadTreeNode<()>>() == 32,
        "QuadTreeNode<()> must be exactly 32 B"
    );
    assert!(
        std::mem::size_of::<QuadTreeNode<u64>>() == 40,
        "QuadTreeNode<u64> must be exactly 40 B"
    );
};
