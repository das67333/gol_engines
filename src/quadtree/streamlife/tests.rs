use super::*;
const SEED: u64 = 42;

#[test]
fn capacity_plan_respects_memory_budget() {
    for mib in [1, 4, 8 * 1024, 20 * 1024, 32 * 1024, 48 * 1024, 64 * 1024, 128 * 1024] {
        let (node_log, node_capacity, cache_log, cache_capacity) = StreamLifeEngine::capacity_plan(mib);
        assert!(node_capacity >= 1usize << node_log);
        assert!(cache_capacity >= 1usize << cache_log);
        let bucket_bytes = std::mem::size_of::<std::sync::atomic::AtomicU32>() as u64;
        let bytes = bucket_bytes * ((1u64 << node_log) + (1u64 << cache_log))
            + node_capacity as u64 * std::mem::size_of::<QuadTreeNode<u64>>() as u64
            + cache_capacity as u64 * std::mem::size_of::<CacheEntry>() as u64;
        assert!(bytes <= u64::from(mib) << 20);
    }
}

#[test]
fn overflow_preserves_state_and_allows_retry() {
    let snapshot = |pattern: &Pattern| {
        (pattern.get_size_log2(), pattern.to_format(crate::PatternFormat::PackedCells).unwrap())
    };
    for topology in [Topology::Unbounded, Topology::Torus] {
        for threads in [1, 2] {
            for failed_step in [0, 1] {
                let mut engine = StreamLifeEngine::new(4, threads);
                engine.load_pattern(&Pattern::random(5, Some(SEED)).unwrap(), topology).unwrap();
                engine.update(0).unwrap();
                let before = engine.current_state();

                // One root entry exceeds this cache's zero soft limit, independently of the pattern.
                let mut cache = std::mem::replace(&mut engine.bicache, BinodeCache::new(0, 1, threads));
                assert!(engine.update(failed_step).is_err());
                assert_eq!(snapshot(&engine.current_state()), snapshot(&before));

                // The saved cache still contains indices from before rollback, so clear it before reuse.
                cache.clear();
                engine.bicache = cache;
                let mut reference = StreamLifeEngine::new(4, threads);
                reference.load_pattern(&before, topology).unwrap();
                assert_eq!(engine.update(0).unwrap(), reference.update(0).unwrap());
                assert_eq!(snapshot(&engine.current_state()), snapshot(&reference.current_state()));
            }
        }
    }
}

#[test]
fn final_merge_overflow_preserves_state_and_allows_smaller_retry() {
    // Opposing, separated gliders leave both output universes nonempty.
    let pattern = Pattern::from_format(
        crate::PatternFormat::RLE,
        b"x = 64, y = 64, rule = B3/S23\n8$9bo$10bo$8b3o$21$48b3o$48bo$49bo!",
    ).unwrap();
    let mut engine = StreamLifeEngine::new(1, 1);
    engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
    let before = engine.current_state();
    let (root, size_log2) = (engine.base.root, engine.base.size_log2);
    assert_eq!(size_log2, 6);

    // Warm only the executor result. The subsequent public update reuses it,
    // so the exhausted store is first encountered by the final root merge.
    engine.base.generations_per_update_log2 = Some(3);
    let (mut dx, mut dy) = (BigInt::ZERO, BigInt::ZERO);
    for _ in 0..engine.base.frames_for_update(3) {
        engine.add_frame(&mut dx, &mut dy).unwrap();
    }
    let framed_size = engine.base.size_log2;
    let blank = engine.base.blank_nodes.get_mut(framed_size, &engine.base.mem);
    let biroot = StreamLifeExecutor::new(&engine, (engine.base.root, blank), framed_size).run(None).unwrap();
    let output_blank = engine.base.blank_nodes.get(framed_size - 1);
    assert!(biroot.0 != output_blank && biroot.1 != output_blank);
    engine.base.root = root;
    engine.base.size_log2 = size_log2;
    for cells in 0.. {
        if engine.base.mem.exceeds_load_factor() {
            break;
        }
        engine.base.mem.find_or_create_leaf_from_u64((1 << 63) | cells);
    }
    assert_eq!(
        algorithm::merge_final_universes(&engine.base.mem, &engine.base.blank_nodes, biroot, framed_size - 1),
        None,
    );
    assert!(engine.update(3).is_err());
    let snapshot = |pattern: &Pattern| {
        (pattern.get_size_log2(), pattern.to_format(crate::PatternFormat::PackedCells).unwrap())
    };
    assert_eq!(snapshot(&engine.current_state()), snapshot(&before));

    let mut reference = StreamLifeEngine::new(1, 1);
    reference.load_pattern(&before, Topology::Unbounded).unwrap();
    assert_eq!(engine.update(0).unwrap(), reference.update(0).unwrap());
    assert_eq!(snapshot(&engine.current_state()), snapshot(&reference.current_state()));
}

#[test]
fn test_pattern_roundtrip() {
    for size_log2 in 3..10 {
        let original = Pattern::random(size_log2, Some(SEED)).unwrap();
        let mut engine = StreamLifeEngine::new(1, 1);
        engine.load_pattern(&original, Topology::Unbounded).unwrap();
        let converted = engine.current_state();

        assert_eq!(
            original.hash(),
            converted.hash(),
            "Pattern roundtrip failed for size 2^{}",
            size_log2
        );
    }
}
