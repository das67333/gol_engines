mod blank;
mod executor;
mod hashlife;
mod hashtable;
mod node;
mod sharded_length;
mod streamlife;

const LEAF_SIZE: u64 = 8;
const LEAF_SIZE_LOG2: u32 = LEAF_SIZE.ilog2();

pub use streamlife::StreamLifeEngine;
pub type HashLifeEngine = hashlife::HashLifeEngine<()>;
