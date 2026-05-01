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
//! The `cache` field is a [`CacheField`] that serves dual purposes:
//! - During processing: type-erased pointer to processing data (defined in executor modules)
//! - After completion: cached result [`Idx`]
//!
//! This space optimization reuses the same memory for both purposes.

use super::hashtable::{CacheField, HashtableSlot, Idx};
use std::{cell::UnsafeCell, sync::atomic::AtomicU8};

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
/// - `cache`: protected by the status bit-set, wraps [`UnsafeCell`]
/// - `status`: atomic bit-set encoding the async state machine
///   (see `super::status`)
/// - `flags`: atomic, combines node metadata and hashtable slot lock
#[derive(Debug, Default)]
pub(super) struct QuadTreeNode<Meta> {
    /// Northwest child or lower 32 bits of leaf cells
    pub(super) nw: Idx,
    /// Northeast child or upper 32 bits of leaf cells
    pub(super) ne: Idx,
    /// Southwest child (unused for leaves)
    pub(super) sw: Idx,
    /// Southeast child (unused for leaves)
    pub(super) se: Idx,
    /// Cache: either processing data pointer or result Idx
    pub(super) cache: CacheField<Idx>,
    /// Processing status (see hashlife_executor for state machine)
    pub(super) status: AtomicU8,
    /// Flags are used in [`NodeStore::find_or_create_inner`]
    flags: AtomicU8,
    /// Meta data for StreamLife (unused in Hashlife)
    pub(super) extra: UnsafeCell<Meta>,
    pub(super) status_extra: AtomicU8,
}

// SAFETY: Sync because atomics handle synchronization and cache is protected by status state machine
unsafe impl<Meta> Sync for QuadTreeNode<Meta> {}

impl<Meta: Default + Sync> HashtableSlot for QuadTreeNode<Meta> {
    fn flags(&self) -> &AtomicU8 {
        &self.flags
    }
}

impl<Meta> QuadTreeNode<Meta> {
    /// Return children as array [nw, ne, sw, se].
    pub(super) fn parts(&self) -> [Idx; 4] {
        [self.nw, self.ne, self.sw, self.se]
    }

    /// Metact leaf cells as 8 bytes (one byte per row).
    ///
    /// Layout: `nw` = rows 0-3, `ne` = rows 4-7
    pub(super) fn leaf_cells(&self) -> [u8; 8] {
        (self.nw as u64 | ((self.ne as u64) << 32)).to_le_bytes()
    }

    /// Metact northwest 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_nw(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.nw >> (i * 8)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Metact northeast 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_ne(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.nw >> (i * 8 + 4)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Metact southwest 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_sw(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.ne >> (i * 8)) & 0xF) << (i * 4);
        }
        result as u16
    }

    /// Metact southeast 4×4 quadrant from 8×8 leaf.
    pub(super) fn leaf_se(&self) -> u16 {
        let mut result = 0;
        for i in 0..4 {
            result |= ((self.ne >> (i * 8 + 4)) & 0xF) << (i * 4);
        }
        result as u16
    }
}
