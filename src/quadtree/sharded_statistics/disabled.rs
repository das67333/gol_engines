use super::MetricKind;
use crossbeam::deque::Steal;

#[derive(Clone, Copy)]
pub struct Ticks;

impl Ticks {
    pub fn now() -> Self {
        Self
    }

    pub fn elapsed_since(self, _start: Ticks) -> Self {
        Self
    }
}

pub struct ExecutionStatistics;

impl ExecutionStatistics {
    pub fn new() -> Self {
        Self
    }

    pub fn merge_from(&mut self, _other: &ExecutionStatistics) {}
}

impl std::fmt::Display for ExecutionStatistics {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

pub fn set_current_execution_stats() {}

pub fn take_current_execution_stats() -> Option<ExecutionStatistics> {
    Some(ExecutionStatistics)
}

pub fn record_status_claim_success() {}

pub fn record_status_claim_fail() {}

pub fn record_metric(_value: u64, _kind: MetricKind) {}

pub fn record_task_duration(_ticks: Ticks) {}

pub fn record_steal<Task>(_result: &Steal<Task>) {}

pub fn record_last_victim_steal<Task>(_result: &Option<Task>) {}
