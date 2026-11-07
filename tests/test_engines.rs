#[cfg(test)]
mod tests {
    use gol_engines::*;

    fn build_engines() -> Vec<Box<dyn GoLEngine>> {
        let data = std::fs::read("res/otca_0.mc.gz").unwrap();
        let pattern = Pattern::from_format(PatternFormat::CompressedMacrocell, &data).unwrap();
        let mem_limit_mib = 64;
        let threads_cnt = 1;
        let mut engines: Vec<Box<dyn GoLEngine>> = vec![
            Box::new(SIMDEngine::new(mem_limit_mib, threads_cnt)),
            Box::new(HashLifeEngine::new(mem_limit_mib, threads_cnt)),
            Box::new(StreamLifeEngine::new(mem_limit_mib, threads_cnt)),
        ];
        for engine in engines.iter_mut() {
            engine.load_pattern(&pattern, Topology::Torus).unwrap();
        }

        assert_fields_equal(&engines);
        engines
    }

    fn assert_fields_equal(engines: &Vec<Box<dyn GoLEngine>>) {
        let first = engines[0].current_state().hash();
        for engine in engines.iter().skip(1) {
            assert_eq!(engine.current_state().hash(), first, "Fields do not match");
        }
    }

    #[test]
    fn test_single_updates() {
        for generations_log2 in 0..7 {
            let mut engines = build_engines();

            for engine in engines.iter_mut() {
                engine.update(generations_log2).unwrap();
            }

            assert_fields_equal(&engines);
        }
    }

    #[test]
    fn test_repetitive_updates_without_gc() {
        let mut engines = build_engines();

        for generations_log2 in 0..7 {
            for engine in engines.iter_mut() {
                engine.update(generations_log2).unwrap();
            }

            assert_fields_equal(&engines);
        }
    }

    #[test]
    fn test_repetitive_updates_with_gc() {
        let mut engines = build_engines();

        for generations_log2 in 0..7 {
            for engine in engines.iter_mut() {
                engine.update(generations_log2).unwrap();
                engine.run_gc();
            }

            assert_fields_equal(&engines);
        }
    }

    #[test]
    fn test_repeated_same_step_on_stationary_pattern() {
        const STATIONARY_RLE: &[u8] =
            b"x = 16, y = 16, rule = B3/S23\n2o12b2o$2o12b2o$12$2o12b2o$2o12b2o!";
        let pattern = Pattern::from_format(PatternFormat::RLE, STATIONARY_RLE).unwrap();
        let expected_hash = pattern.hash();

        for &threads_cnt in &[1usize, 2, 4] {
            for engine_kind in ["hashlife", "streamlife"] {
                let mut engine: Box<dyn GoLEngine> = match engine_kind {
                    "hashlife" => Box::new(HashLifeEngine::new(64, threads_cnt)),
                    "streamlife" => Box::new(StreamLifeEngine::new(64, threads_cnt)),
                    _ => unreachable!(),
                };
                engine.load_pattern(&pattern, Topology::Unbounded).unwrap();

                for update_idx in 0..3 {
                    engine.update(4).unwrap();
                    assert_eq!(
                        engine.current_state().hash(),
                        expected_hash,
                        "{engine_kind} threads={threads_cnt} update={update_idx} changed a stationary pattern"
                    );
                }
            }
        }
    }

    /// Multi-threaded consistency: the parallel executors must produce the
    /// same result regardless of thread count. Exercises the StreamLife
    /// async cross-engine work-stealing path (the binode → HashLife task
    /// dependency chain only fires when multiple workers can race).
    #[test]
    fn test_multithread_consistency() {
        let data = std::fs::read("res/otca_0.mc.gz").unwrap();
        let pattern = Pattern::from_format(PatternFormat::CompressedMacrocell, &data).unwrap();
        let mem_limit_mib = 64;

        for generations_log2 in [0u32, 3, 6] {
            let mut reference: Option<u64> = None;
            for &threads_cnt in &[1usize, 2, 4, 8] {
                for engine_kind in ["hashlife", "streamlife"] {
                    let mut engine: Box<dyn GoLEngine> = match engine_kind {
                        "hashlife" => Box::new(HashLifeEngine::new(mem_limit_mib, threads_cnt)),
                        "streamlife" => Box::new(StreamLifeEngine::new(mem_limit_mib, threads_cnt)),
                        _ => unreachable!(),
                    };
                    engine.load_pattern(&pattern, Topology::Torus).unwrap();
                    engine.update(generations_log2).unwrap();
                    let h = engine.current_state().hash();
                    match reference {
                        None => reference = Some(h),
                        Some(r) => assert_eq!(
                            h, r,
                            "{engine_kind} threads={threads_cnt} gens_log2={generations_log2} mismatch"
                        ),
                    }
                }
            }
        }
    }

    #[test]
    fn test_low_memory_updates_or_preserves_state_for_retry() {
        let pattern = Pattern::random(8, Some(42)).unwrap();
        let expected = |step| {
            let mut reference = HashLifeEngine::new(64, 1);
            reference.load_pattern(&pattern, Topology::Unbounded).unwrap();
            reference.update(step).unwrap();
            reference.current_state().hash()
        };
        let (expected_one, expected_large) = (expected(0), expected(10));
        for workers in [1, 2, 4, 8, 45] {
            let engines: [Box<dyn GoLEngine>; 2] = [
                Box::new(HashLifeEngine::new(4, workers)),
                Box::new(StreamLifeEngine::new(4, workers)),
            ];
            for mut engine in engines {
                engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
                let before = engine.current_state().hash();
                if engine.update(10).is_ok() {
                    assert_eq!(engine.current_state().hash(), expected_large, "workers={workers}");
                } else {
                    assert_eq!(engine.current_state().hash(), before, "workers={workers} changed the saved pattern");
                    engine.update(0).unwrap();
                    assert_eq!(engine.current_state().hash(), expected_one, "workers={workers} retry differs from HashLife");
                }
            }
        }
    }

    #[test]
    fn parallel_collection_preserves_future_updates() {
        let pattern = Pattern::random(7, Some(42)).unwrap();
        for topology in [Topology::Unbounded, Topology::Torus] {
            for workers in [1, 4, 16] {
                let engines: Vec<Box<dyn GoLEngine>> = vec![
                    Box::new(HashLifeEngine::new(64, workers)),
                    Box::new(StreamLifeEngine::new(64, workers)),
                ];
                for mut engine in engines {
                    engine.load_pattern(&pattern, topology).unwrap();
                    for step in [0, 3, 1] {
                        let before = engine.current_state();
                        let mut reference = HashLifeEngine::new(64, 1);
                        reference.load_pattern(&before, topology).unwrap();
                        let expected_offset = reference.update(step).unwrap();
                        engine.run_gc();
                        assert_eq!(engine.current_state().hash(), before.hash());
                        assert_eq!(engine.update(step).unwrap(), expected_offset);
                        assert_eq!(
                            engine.current_state().hash(),
                            reference.current_state().hash()
                        );
                    }
                }
            }
        }
    }
}
