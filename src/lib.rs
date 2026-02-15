#![warn(clippy::all)]

mod pattern;
mod quadtree;
mod simd;
mod topology;
mod traits;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

pub use num_bigint::BigInt;
pub use pattern::{Pattern, PatternFormat, PatternNode};
pub use topology::Topology;
pub use traits::GoLEngine;

pub use quadtree::{HashLifeEngine, StreamLifeEngine};
pub use simd::SIMDEngine;

pub type DefaultEngine = HashLifeEngine;

pub const VERSION: &str = "0.2.1";
