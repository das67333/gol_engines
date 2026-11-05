use gol_engines::{GoLEngine, Pattern, PatternFormat, SIMDEngine, StreamLifeEngine, Topology};

#[test]
fn repeated_low_memory_recovery_matches_simd() {
    let packed = |p: Pattern| p.to_format(PatternFormat::PackedCells).unwrap();
    for workers in [1, 4] {
        for seed in 0..8 {
            let pattern = Pattern::random(7, Some(seed)).unwrap();
            let mut engine = StreamLifeEngine::new(2, workers);
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
                assert_eq!(packed(engine.current_state()), packed(reference.current_state()), "workers={workers}, seed={seed}, step={step}");
            }
        }
    }
}
