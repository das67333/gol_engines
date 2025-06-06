mod blank;
mod hashlife;
mod memory;
mod node;
mod streamlife;
mod streamlife_cache;

const LEAF_SIZE: u64 = 8;
const LEAF_SIZE_LOG2: u32 = LEAF_SIZE.ilog2();

use blank::BlankNodes;
use memory::{MemoryManager, PrefetchedNode};
use node::{NodeIdx, QuadTreeNode};
use streamlife_cache::{CacheEntry, StreamLifeCache};

pub use streamlife::StreamLifeEngineSync;
pub type HashLifeEngineSync = hashlife::HashLifeEngineSync<()>;
