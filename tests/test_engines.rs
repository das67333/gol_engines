#[cfg(test)]
mod tests {
    use gol_engines::*;
    use serial_test::serial;

    fn build_engines() -> Vec<Box<dyn GoLEngine>> {
        let data = std::fs::read("../res/otca_0.mc.gz").unwrap();
        let pattern = Pattern::from_format(PatternFormat::CompressedMacrocell, &data).unwrap();
        let mem_limit_mib = 16;
        let mut engines: Vec<Box<dyn GoLEngine>> = vec![
            Box::new(SIMDEngine::new(mem_limit_mib)),
            Box::new(HashLifeEngineSmall::new(mem_limit_mib)),
            Box::new(StreamLifeEngineSmall::new(mem_limit_mib)),
            Box::new(HashLifeEngineSync::new(mem_limit_mib)),
            Box::new(StreamLifeEngineSync::new(mem_limit_mib)),
            Box::new(HashLifeEngineAsync::new(mem_limit_mib)),
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
    #[serial]
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
    #[serial]
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
    #[serial]
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
}
