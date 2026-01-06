mod blank;
mod hashlife;
mod hashlife_executor;
mod memory;
mod node;
mod statistics;
// mod streamlife;
// mod streamlife_cache;

mod status {
    pub(super) const NOT_STARTED: u8 = 0;
    pub(super) const PROCESSING: u8 = 1;
    pub(super) const PENDING: u8 = 2;
    pub(super) const FINISHED: u8 = 3;
}

const LEAF_SIZE: u64 = 8;
const LEAF_SIZE_LOG2: u32 = LEAF_SIZE.ilog2();

use blank::BlankNodes;
use memory::MemoryManager;
use node::{NodeIdx, QuadTreeNode};
use statistics::{ExecutionStatistics, TasksCountGuard};
// use streamlife_cache::{CacheEntry, StreamLifeCache};

// pub use streamlife::StreamLifeEngineAsync;
pub type HashLifeEngineAsync = hashlife::HashLifeEngineAsync<()>;
