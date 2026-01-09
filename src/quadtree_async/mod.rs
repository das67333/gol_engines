mod blank;
mod hashlife;
mod hashlife_executor;
mod memory;
mod node;
mod statistics;
mod streamlife;
mod streamlife_cache;

const LEAF_SIZE: u64 = 8;
const LEAF_SIZE_LOG2: u32 = LEAF_SIZE.ilog2();

pub use streamlife::StreamLifeEngineAsync;
pub type HashLifeEngineAsync = hashlife::HashLifeEngineAsync<()>;
