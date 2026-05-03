use super::MetricKind;
use crossbeam::deque::Steal;

#[derive(Clone, Copy)]
pub struct Ticks;

impl Ticks {
    #[inline(always)]
    pub fn now() -> Self {
        Self
    }

    #[inline(always)]
    pub fn elapsed_since(self, _start: Ticks) -> Self {
        Self
    }
}

pub struct ExecutionStatistics;

impl ExecutionStatistics {
    #[inline(always)]
    pub fn new() -> Self {
        Self
    }

    #[inline(always)]
    pub fn merge_from(&mut self, _other: &ExecutionStatistics) {}
}

impl std::fmt::Display for ExecutionStatistics {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

#[inline(always)]
pub fn set_current_execution_stats() {}

#[inline(always)]
pub fn take_current_execution_stats() -> Option<ExecutionStatistics> {
    Some(ExecutionStatistics)
}

#[inline(always)]
pub fn record_status_claim_success() {}

#[inline(always)]
pub fn record_status_claim_fail() {}

#[inline(always)]
pub fn record_metric(_value: u64, _kind: MetricKind) {}

#[inline(always)]
pub fn record_task_duration(_ticks: Ticks) {}

#[inline(always)]
pub fn record_steal<Task>(_result: &Steal<Task>) {}

#[inline(always)]
pub fn record_last_victim_steal<Task>(_result: &Option<Task>) {}
