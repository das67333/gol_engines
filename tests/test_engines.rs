use gol_engines::*;

fn otca_pattern() -> Pattern {
    let data = std::fs::read("res/otca_0.mc.gz").unwrap();
    Pattern::from_format(PatternFormat::CompressedMacrocell, &data).unwrap()
}

fn quadtree_engines(mem_limit_mib: u32, workers: usize) -> [Box<dyn GoLEngine>; 2] {
    [
        Box::new(HashLifeEngine::new(mem_limit_mib, workers)),
        Box::new(StreamLifeEngine::new(mem_limit_mib, workers)),
    ]
}

#[test]
fn pattern_roundtrips() {
    for size_log2 in 4..10 {
        let pattern = Pattern::random(size_log2, Some(42)).unwrap();
        let mut engines: Vec<_> = quadtree_engines(1, 1)
            .into_iter()
            .map(|e| (e, Topology::Unbounded))
            .collect();
        if size_log2 >= 7 {
            engines.push((Box::new(SIMDEngine::new(1, 1)), Topology::Torus));
        }
        for (mut engine, topology) in engines {
            engine.load_pattern(&pattern, topology).unwrap();
            let restored = engine.current_state();
            assert_eq!(restored.hash(), pattern.hash(), "size={size_log2}");
        }
    }
}

#[test]
fn single_updates_match_simd_across_worker_counts() {
    let pattern = otca_pattern();
    let mut reference = SIMDEngine::new(64, 1);
    for step in 0..7 {
        reference.load_pattern(&pattern, Topology::Torus).unwrap();
        reference.update(step).unwrap();
        let expected = reference.current_state().hash();
        for workers in [1, 2, 4, 8] {
            if workers != 1 && ![0, 3, 6].contains(&step) {
                continue;
            }
            for mut engine in quadtree_engines(64, workers) {
                engine.load_pattern(&pattern, Topology::Torus).unwrap();
                engine.update(step).unwrap();
                assert_eq!(
                    engine.current_state().hash(),
                    expected,
                    "workers={workers}, step={step}"
                );
            }
        }
    }
}

#[test]
fn repeated_updates_match_simd_with_and_without_gc() {
    let pattern = otca_pattern();
    let mut reference = SIMDEngine::new(64, 1);
    reference.load_pattern(&pattern, Topology::Torus).unwrap();
    let expected: Vec<_> = (0..7)
        .map(|step| {
            reference.update(step).unwrap();
            reference.current_state().hash()
        })
        .collect();
    for collect in [false, true] {
        for mut engine in quadtree_engines(64, 1) {
            engine.load_pattern(&pattern, Topology::Torus).unwrap();
            for (step, &hash) in expected.iter().enumerate() {
                engine.update(step as u32).unwrap();
                if collect {
                    engine.run_gc();
                }
                assert_eq!(engine.current_state().hash(), hash, "gc={collect}, step={step}");
            }
        }
    }
}

#[test]
fn repeated_same_step_preserves_a_stationary_pattern() {
    let pattern = Pattern::from_format(
        PatternFormat::RLE,
        b"x = 16, y = 16, rule = B3/S23\n2o12b2o$2o12b2o$12$2o12b2o$2o12b2o!",
    )
    .unwrap();
    let expected = pattern.hash();
    for workers in [1, 2, 4] {
        for mut engine in quadtree_engines(64, workers) {
            engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
            for update in 0..3 {
                engine.update(4).unwrap();
                assert_eq!(
                    engine.current_state().hash(),
                    expected,
                    "workers={workers}, update={update}"
                );
            }
        }
    }
}

#[test]
fn low_memory_updates_or_preserves_state_for_retry() {
    let pattern = Pattern::random(8, Some(42)).unwrap();
    let expected = |step| {
        let mut reference = HashLifeEngine::new(64, 1);
        reference.load_pattern(&pattern, Topology::Unbounded).unwrap();
        reference.update(step).unwrap();
        reference.current_state().hash()
    };
    let (expected_one, expected_large) = (expected(0), expected(10));
    for workers in [1, 2, 4, 8, 45] {
        for mut engine in quadtree_engines(4, workers) {
            engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
            let before = engine.current_state().hash();
            if engine.update(10).is_ok() {
                assert_eq!(engine.current_state().hash(), expected_large, "workers={workers}");
            } else {
                assert_eq!(
                    engine.current_state().hash(),
                    before,
                    "workers={workers} changed the saved pattern"
                );
                engine.update(0).unwrap();
                assert_eq!(
                    engine.current_state().hash(),
                    expected_one,
                    "workers={workers} retry differs"
                );
            }
        }
    }
}

#[test]
fn parallel_collection_preserves_future_updates() {
    let pattern = Pattern::random(7, Some(42)).unwrap();
    let steps = [0, 3, 1];
    for topology in [Topology::Unbounded, Topology::Torus] {
        let mut expected = Vec::new();
        let mut before = pattern.clone();
        // Fresh reference engines avoid exercising the GC being checked.
        for step in steps {
            let mut reference = HashLifeEngine::new(64, 1);
            reference.load_pattern(&before, topology).unwrap();
            let offset = reference.update(step).unwrap();
            before = reference.current_state();
            expected.push((offset, before.hash()));
        }
        for workers in [1, 4, 16] {
            for mut engine in quadtree_engines(64, workers) {
                engine.load_pattern(&pattern, topology).unwrap();
                for (&step, (offset, hash)) in steps.iter().zip(&expected) {
                    let before = engine.current_state().hash();
                    engine.run_gc();
                    assert_eq!(engine.current_state().hash(), before);
                    assert_eq!(&engine.update(step).unwrap(), offset);
                    assert_eq!(engine.current_state().hash(), *hash, "workers={workers}, step={step}");
                }
            }
        }
    }
}
