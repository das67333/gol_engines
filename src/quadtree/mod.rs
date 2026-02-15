mod binode_cache;
mod blank;
mod hashlife;
mod hashlife_executor;
mod node;
mod node_store;
mod sharded_length;
mod streamlife;
mod streamlife_executor;

const LEAF_SIZE: u64 = 8;
const LEAF_SIZE_LOG2: u32 = LEAF_SIZE.ilog2();

mod status {
    pub(super) const NOT_STARTED: u8 = 0;
    pub(super) const PROCESSING: u8 = 1;
    pub(super) const PENDING: u8 = 2;
    pub(super) const FINISHED: u8 = 3;
}

pub use streamlife::StreamLifeEngine;
pub type HashLifeEngine = hashlife::HashLifeEngine<()>;
