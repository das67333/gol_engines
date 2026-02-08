#![warn(clippy::all)]

mod pattern;
mod quadtree_async;
mod quadtree_small;
mod quadtree_sync;
mod simd;
mod topology;
mod traits;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

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
