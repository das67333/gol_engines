#![warn(clippy::all, clippy::cargo)]

mod pattern;
mod quadtree_async;
mod quadtree_small;
mod quadtree_sync;
mod simd;
mod topology;
mod traits;

pub use pattern::{Pattern, PatternFormat, PatternNode};
pub use topology::Topology;
pub use traits::GoLEngine;

pub use quadtree_async::{HashLifeEngineAsync, StreamLifeEngineAsync};
pub use quadtree_small::{HashLifeEngineSmall, StreamLifeEngineSmall};
pub use quadtree_sync::{HashLifeEngineSync, StreamLifeEngineSync};
pub use simd::SIMDEngine;

pub type DefaultEngine = SIMDEngine;

pub const VERSION: &str = "1.0";

use std::sync::atomic::{AtomicU32, AtomicU64};
pub static WORKER_THREADS: AtomicU32 = AtomicU32::new(0);
pub static MIN_TASK_SPAWN_SIZE_LOG2: AtomicU32 = AtomicU32::new(12);
pub const MAX_TASKS_COUNT: u64 = 1024;
pub static TASKS_SPAWN_COUNT: AtomicU64 = AtomicU64::new(0);
pub static NODES_CREATED_COUNT: AtomicU64 = AtomicU64::new(0);
