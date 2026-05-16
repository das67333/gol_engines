mod algorithm;
mod blank;
mod executors;
mod hashlife;
mod hashtable;
mod node;
mod sharded_statistics;
mod spin;
mod streamlife;

const LEAF_SIZE: u64 = 8;
const LEAF_SIZE_LOG2: u32 = LEAF_SIZE.ilog2();

/// Status bits encoded into the `AtomicU8` carried by every node / cache entry.
///
/// The async parallel executors interpret the byte as a small bit-set so that
/// independent transitions (work-status, pending-state, finished, dependents-lock)
/// can be manipulated atomically without ever masking each other.
///
/// Async lifecycle of a single node
/// ```text
///     NOT_STARTED ── CAS ──► PROCESSING ── store ──► PENDING
///                            (init barrier;          (pd installed;
///                             pd not yet            pushers may grab
///                             installed)            DEPS_LOCK)
///                                                  ▲          │
///                                       fetch_xor  │          │ CAS preserving DEPS_LOCK
///                                                  │          ▼
///                                                ACTIVE (owner is computing)
///                                                  │
///                                                  │ CAS (DEPS_LOCK==0)
///                                                  ▼
///                                              PROCESSING ── store ──► FINISHED
///                                              (finish barrier)
/// ```
///
/// `PROCESSING` doubles as the brief barrier phase at both ends of an async
/// node's life: pushers always treat it as "wait until something else", so the
/// owner can install or drain `ProcessingData` without concurrent access.
///
/// `PROCESSING` and `FINISHED` are also the only states reachable on the legacy
/// synchronous code paths in [`algorithm`] (and on `status_extra` for lane
/// descriptors). Those paths never see `PENDING`, `ACTIVE`, or `DEPS_LOCK`, so
/// the bit-flag encoding is fully compatible: they simply write/compare the
/// same constants.
mod status {
    pub const NOT_STARTED: u8 = 0;
    /// Brief, exclusive barrier. Used for both async init (between claim and
    /// publication of `ProcessingData`) and async finish (between draining the
    /// dependents list and publishing the cached value). Pushers spin while
    /// this bit is set. Also used by the synchronous code paths.
    pub const PROCESSING: u8 = 0b0000_0001;
    /// `ProcessingData` is installed and no thread is actively computing the
    /// node. Pushers may register dependents under [`DEPS_LOCK`].
    pub const PENDING: u8 = 0b0000_0010;
    /// A worker is actively computing the node (owner-mutex). Pushers may
    /// still register dependents under [`DEPS_LOCK`] in parallel.
    pub const ACTIVE: u8 = 0b0000_0100;
    /// Result is published in the cache and the dependents list has been
    /// drained. Terminal state.
    pub const FINISHED: u8 = 0b0000_1000;
    /// Transient overlay bit: a thread is currently mutating the dependents
    /// list. Layered on top of `PENDING` or `ACTIVE`.
    pub const DEPS_LOCK: u8 = 0b0001_0000;
}

pub use streamlife::StreamLifeEngine;
pub type HashLifeEngine = hashlife::HashLifeEngine<()>;
