use gol_engines::{GoLEngine, HashLifeEngine, Pattern, PatternFormat, SIMDEngine, StreamLifeEngine, Topology};

#[test]
fn repeated_low_memory_recovery_matches_simd() {
    let packed = |p: Pattern| p.to_format(PatternFormat::PackedCells).unwrap();
    for workers in [1, 4] {
        for seed in 0..8 {
            let pattern = Pattern::random(7, Some(seed)).unwrap();
            let engines: [Box<dyn GoLEngine>; 2] = [
                Box::new(HashLifeEngine::new(2, workers)),
                Box::new(StreamLifeEngine::new(2, workers)),
            ];
            for mut engine in engines {
                let mut reference = SIMDEngine::new(2, 1);
                engine.load_pattern(&pattern, Topology::Torus).unwrap();
                reference.load_pattern(&pattern, Topology::Torus).unwrap();
                for step in [8, 0, 8, 0, 6, 1, 6, 1, 4, 0, 4, 0, 8, 2, 8, 0] {
                    let before = packed(engine.current_state());
                    if engine.update(step).is_ok() {
                        reference.update(step).unwrap();
                    } else {
                        assert_eq!(packed(engine.current_state()), before);
                    }
                    assert_eq!(
                        packed(engine.current_state()),
                        packed(reference.current_state()),
                        "workers={workers}, seed={seed}, step={step}"
                    );
                }
            }
        }
    }
}

#[test]
fn hashlife_completes_with_a_small_cache() {
    let pattern = Pattern::random(8, Some(42)).unwrap();
    for workers in [1, 4] {
        let mut engine = HashLifeEngine::new(2, workers);
        let mut reference = SIMDEngine::new(2, 1);
        engine.load_pattern(&pattern, Topology::Torus).unwrap();
        reference.load_pattern(&pattern, Topology::Torus).unwrap();
        for step in [8, 8, 0, 6] {
            engine.update(step).unwrap();
            reference.update(step).unwrap();
            assert_eq!(
                engine.current_state().to_format(PatternFormat::PackedCells).unwrap(),
                reference.current_state().to_format(PatternFormat::PackedCells).unwrap(),
                "workers={workers}, step={step}"
            );
        }
    }
}

#[test]
fn cancellation_preserves_the_input_and_allows_another_update() {
    use gol_engines::UpdateCancelled;
    use std::time::Duration;
    let pattern = Pattern::random(10, Some(42)).unwrap();
    let packed = |p: Pattern| p.to_format(PatternFormat::PackedCells).unwrap();
    for workers in [1, 4] {
        let engines: [Box<dyn GoLEngine>; 2] = [
            Box::new(HashLifeEngine::new(128, workers)),
            Box::new(StreamLifeEngine::new(128, workers)),
        ];
        for mut engine in engines {
            engine.load_pattern(&pattern, Topology::Torus).unwrap();
            let token = engine.cancellation_token().unwrap();
            token.cancel();
            assert!(engine.update(20).unwrap_err().is::<UpdateCancelled>());
            token.reset();
            for _ in 0..2 {
                let before = packed(engine.current_state());
                let error = std::thread::scope(|scope| {
                    scope.spawn(|| {
                        std::thread::sleep(Duration::from_millis(10));
                        token.cancel();
                    });
                    engine.update(20)
                })
                .unwrap_err();
                assert!(error.is::<UpdateCancelled>(), "{error:#}");
                assert_eq!(packed(engine.current_state()), before);
                token.reset();
                let mut reference = SIMDEngine::new(128, 1);
                reference
                    .load_pattern(&engine.current_state(), Topology::Torus)
                    .unwrap();
                assert_eq!(engine.update(3).unwrap(), reference.update(3).unwrap());
                assert_eq!(packed(engine.current_state()), packed(reference.current_state()));
            }
        }
    }
}
