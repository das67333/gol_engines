mod blank;
mod hashlife;
mod memory;
mod node;
mod statistics;
mod streamlife;

const LEAF_SIZE: u64 = 8;
const LEAF_SIZE_LOG2: u32 = LEAF_SIZE.ilog2();

use blank::BlankNodes;
use memory::MemoryManager;
use node::{NodeIdx, QuadTreeNode};
use statistics::{ExecutionStatistics, TasksCountGuard};

pub use streamlife::StreamLifeEngineAsync;
pub type HashLifeEngineAsync = hashlife::HashLifeEngineAsync<()>;
