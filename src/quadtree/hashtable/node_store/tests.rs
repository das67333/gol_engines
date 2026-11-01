use super::*;
use std::collections::HashSet;

#[test]
fn gc_drops_invalidated_results_but_keeps_structural_children() {
    let mut store = NodeStore::<u64>::new(8, 200, 1);
    let children = [1, 2, 3, 4].map(|value| store.find_or_create_leaf_from_u64(value));
    let root = store.find_or_create_node(children[0], children[1], children[2], children[3]);
    let result = store.find_or_create_leaf_from_u64(99);
    store.get(root).cache.set_value(result);
    store
        .get(root)
        .status
        .store(status::FINISHED, Ordering::Relaxed);

    store.gc(&[root], crate::quadtree::LEAF_SIZE_LOG2 + 1);

    assert_eq!(store.len(), 5);
    assert_eq!(
        store.get(root).status.load(Ordering::Relaxed),
        status::NOT_STARTED
    );
    for (value, idx) in (1..=4).zip(children) {
        assert_eq!(store.find_or_create_leaf_from_u64(value), idx);
    }
    store.find_or_create_leaf_from_u64(99);
    assert_eq!(store.len(), 6);
}

#[test]
fn high_load_survives_gc_and_slot_reuse() {
    let mut store = NodeStore::<u64>::new(12, 10_000, 4);
    let copies = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..4)
            .map(|shard| {
                let store = &store;
                scope.spawn(move || {
                    let mem = store.create_ref(shard);
                    (0..6_000)
                        .map(|key| mem.find_or_create_leaf_from_u64(key))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap())
            .collect::<Vec<_>>()
    });
    assert!(copies.iter().all(|copy| copy == &copies[0]));
    assert_eq!(store.len(), 6_000);
    assert!(!store.exceeds_load_factor());

    let roots = &copies[0][..64];
    let dead: HashSet<_> = copies[0][64..].iter().copied().collect();
    store.gc(roots, crate::quadtree::LEAF_SIZE_LOG2);
    assert_eq!(store.len(), roots.len());
    for (key, &idx) in roots.iter().enumerate() {
        assert_eq!(store.find_or_create_leaf_from_u64(key as u64), idx);
    }
    let replacements = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..4)
            .map(|shard| {
                let store = &store;
                scope.spawn(move || {
                    let mem = store.create_ref(shard);
                    (0..1_500)
                        .map(|key| {
                            mem.find_or_create_leaf_from_u64(
                                10_000 + 1_500 * shard as u64 + key,
                            )
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect::<Vec<_>>()
    });
    assert_eq!(store.len(), 6_064);
    assert_eq!(replacements.iter().collect::<HashSet<_>>().len(), 6_000);
    assert!(replacements.iter().any(|idx| dead.contains(idx)));
    for (offset, &idx) in replacements.iter().enumerate() {
        assert_eq!(
            store.find_or_create_leaf_from_u64(10_000 + offset as u64),
            idx
        );
    }
    store.clear();
    store.find_or_create_leaf_from_u64(42);
    assert_eq!(store.len(), 1);
}
