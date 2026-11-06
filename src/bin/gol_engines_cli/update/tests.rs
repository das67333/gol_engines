use super::advance;
use anyhow::bail;

#[test]
fn smaller_steps_finish_all_requested_generations() {
    for initial_step in [1, 2, 3] {
        let mut generations = 0;
        advance(initial_step, initial_step, |step| {
            if step != 0 {
                bail!("simulated memory limit");
            }
            generations += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(generations, 1 << initial_step);
    }
}

#[test]
fn minimum_step_failure_returns_the_engine_error() {
    for initial_step in [0, 1, 3] {
        let error = advance(initial_step, initial_step, |_| bail!("simulated memory limit")).unwrap_err();
        assert!(error.to_string().contains("one generation"));
        assert_eq!(error.root_cause().to_string(), "simulated memory limit");
    }
}

#[test]
fn one_failure_after_success_retries_without_reducing_the_step() {
    let mut attempts = 0;
    let mut generations = 0;
    advance(2, 1, |step| {
        assert_eq!(step, 1);
        attempts += 1;
        if attempts == 2 {
            bail!("simulated memory limit");
        }
        generations += 1 << step;
        Ok(())
    })
    .unwrap();
    assert_eq!(generations, 4);
}
