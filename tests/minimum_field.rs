use gol_engines::{GoLEngine, HashLifeEngine, Pattern, StreamLifeEngine, Topology};

#[test]
fn undersized_fields_are_rejected_without_changing_the_loaded_pattern() {
    let valid = Pattern::random(4, Some(42)).unwrap();
    let small = Pattern::random(3, Some(42)).unwrap();
    for topology in [Topology::Unbounded, Topology::Torus] {
        let engines: [Box<dyn GoLEngine>; 2] = [
            Box::new(HashLifeEngine::new(1, 1)),
            Box::new(StreamLifeEngine::new(1, 1)),
        ];
        for mut engine in engines {
            engine.load_pattern(&valid, topology).unwrap();
            engine.update(0).unwrap();
            let before = engine.current_state().hash();
            let error = engine.load_pattern(&small, topology).unwrap_err();
            assert!(error.to_string().contains("16x16"));
            assert_eq!(engine.current_state().hash(), before);
            engine.update(0).unwrap();
        }
    }
}

#[test]
fn new_quadtree_engines_have_an_updatable_empty_field() {
    let engines: [Box<dyn GoLEngine>; 2] = [
        Box::new(HashLifeEngine::new(1, 1)),
        Box::new(StreamLifeEngine::new(1, 1)),
    ];
    for mut engine in engines {
        assert_eq!(engine.current_state().get_size_log2(), 4);
        for step in [0, 1, 4] {
            engine.update(step).unwrap();
            let pattern = engine.current_state();
            assert_eq!(pattern.get_size_log2(), 4);
            assert_eq!(pattern.population(), 0.into());
        }
    }
}
