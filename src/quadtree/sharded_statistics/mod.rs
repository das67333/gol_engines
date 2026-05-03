mod sharded_length;
pub(super) use sharded_length::{LengthShard, ShardedLength};

cfg_select! {
    feature = "statistics" => {
        mod enabled;
        pub(super) use enabled::*;
    }
    _ => {
        mod disabled;
        pub(super) use disabled::*;
    }
}

/// Metric kind for log2 histogram distributions.
/// Spin-count metrics store raw spin iterations.
/// TaskDuration stores raw timer ticks.
#[derive(Clone, Copy)]
pub(super) enum MetricKind {
    // PENDING -> PROCESSING status acquire (spin count)
    ProcessTask = 0,
    NotifyDep = 1,
    HandleDep = 2,
    HandleBiDep = 3,
    // Algorithm spin-wait on FINISHED (spin count)
    Node2Lanes = 4,
    // Task duration (raw timer ticks)
    #[allow(dead_code)]
    TaskDuration = 5,
}
