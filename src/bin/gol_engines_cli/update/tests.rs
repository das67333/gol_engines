use super::{Progress, advance};
use anyhow::bail;
use gol_engines::UpdateCancelled;
use num_bigint::BigInt;

#[test]
fn smaller_steps_finish_all_requested_generations() {
    for initial_step in [0, 1, 2, 3] {
        let mut progress = Progress::new(initial_step, initial_step);
        let mut can_retry = false;
        while let Some(mut step) = progress.next_step() {
            advance(&mut step, &mut can_retry, |step| {
                if step > 1 {
                    bail!("simulated memory limit");
                }
                Ok([BigInt::ZERO, BigInt::ZERO])
            })
            .unwrap();
            progress.step_log2 = step;
            progress.generation += BigInt::from(1) << step;
        }
        assert_eq!(progress.generation, progress.target);
    }
}

#[test]
fn terminal_steps_return_the_engine_error_without_further_reduction() {
    for mut step in [0, 1] {
        let mut attempts = 0;
        let error = advance(&mut step, &mut false, |_| {
            attempts += 1;
            bail!("simulated memory limit")
        })
        .unwrap_err();
        assert_eq!(attempts, 1);
        assert!(error.to_string().contains("minimum step"));
        assert_eq!(error.root_cause().to_string(), "simulated memory limit");
    }
}

#[test]
fn one_failure_after_success_retries_without_reducing_the_step() {
    let mut step = 1;
    let mut can_retry = false;
    advance(&mut step, &mut can_retry, |_| Ok([BigInt::ZERO, BigInt::ZERO])).unwrap();
    let mut attempts = 0;
    advance(&mut step, &mut can_retry, |s| {
        assert_eq!(s, 1);
        attempts += 1;
        if attempts == 1 {
            bail!("simulated memory limit");
        }
        Ok([BigInt::ZERO, BigInt::ZERO])
    })
    .unwrap();
    assert_eq!(attempts, 2);
}

#[test]
fn cancellation_is_never_retried_as_memory_pressure() {
    let mut attempts = 0;
    let error = advance(&mut 8, &mut true, |_| {
        attempts += 1;
        Err(UpdateCancelled.into())
    })
    .unwrap_err();
    assert!(error.is::<UpdateCancelled>());
    assert_eq!(attempts, 1);
}

#[test]
fn resumed_run_stops_at_the_exact_target() {
    let mut progress = Progress::new(6, 4);
    progress.generation = BigInt::from(55);
    while let Some(step) = progress.next_step() {
        progress.generation += BigInt::from(1) << step;
    }
    assert_eq!(progress.generation, progress.target);
}
