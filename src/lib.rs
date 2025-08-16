#![warn(clippy::all)]

mod pattern;
mod quadtree_async;
mod quadtree_small;
mod quadtree_sync;
mod simd;
mod topology;
mod traits;

pub use num_bigint::BigInt;
pub use pattern::{Pattern, PatternFormat, PatternNode};
pub use topology::Topology;
pub use traits::GoLEngine;

pub use quadtree_async::{HashLifeEngineAsync, StreamLifeEngineAsync};
pub use quadtree_small::{HashLifeEngineSmall, StreamLifeEngineSmall};
pub use quadtree_sync::{HashLifeEngineSync, StreamLifeEngineSync};
pub use simd::SIMDEngine;

pub type DefaultEngine = HashLifeEngineAsync;

pub const VERSION: &str = "0.2.1";

use std::sync::atomic::{AtomicU32, AtomicU64};
pub static WORKER_THREADS: AtomicU32 = AtomicU32::new(0);
pub const MIN_TASK_SPAWN_SHIFT: u32 = 5;
pub const MAX_TASKS_COUNT: u64 = 1024;
pub static TASKS_SPAWNED_COUNT: AtomicU64 = AtomicU64::new(0);
