use super::*;
use crate::quadtree::hashtable::NodeStore;

fn lane_test_tile(mem: &NodeStore<u64>, blanks: &mut BlankNodes) -> Idx {
    let empty = blanks.get_mut(LEAF_SIZE_LOG2, mem);
    let glider = mem.find_or_create_leaf_from_u64((1 << 10) | (1 << 19) | (7 << 25));
    let corner = mem.find_or_create_node(empty, empty, empty, glider);
    let empty = blanks.get_mut(LEAF_SIZE_LOG2 + 1, mem);
    blanks.get_mut(LEAF_SIZE_LOG2 + 2, mem);
    mem.find_or_create_node(corner, empty, empty, empty)
}

#[test]
fn lane_classification_cancels_and_allows_concurrent_retry() {
    let size_log2 = LEAF_SIZE_LOG2 + 2;
    let reference = NodeStore::<u64>::new(12, 4096, 4);
    let mut reference_blanks = BlankNodes::new();
    let root = lane_test_tile(&reference, &mut reference_blanks);
    let expected = node2lanes(&reference, &reference_blanks, root, size_log2).unwrap();
    assert_ne!(
        expected & 0xff,
        0,
        "the tile must require directional classification"
    );

    // Discover the cancellation boundary, independently of length-shard batching.
    let probe = NodeStore::<u64>::new(12, 4096, 4);
    for cells in 0.. {
        if probe.exceeds_load_factor() {
            break;
        }
        probe.find_or_create_leaf_from_u64((1 << 63) | cells);
    }
    let last_available = probe.len() - 1;
    let mut mem = NodeStore::<u64>::new(12, 4096, 4);
    let mut blanks = BlankNodes::new();
    let root = lane_test_tile(&mem, &mut blanks);
    for cells in 0.. {
        if mem.len() == last_available {
            break;
        }
        mem.find_or_create_leaf_from_u64((1 << 63) | cells);
    }
    assert!(!mem.exceeds_load_factor());
    assert_eq!(node2lanes(&mem, &blanks, root, size_log2), None);
    assert!(mem.exceeds_load_factor());

    // Collection preserves completed lane descriptors; unfinished claims must
    // therefore be released by cancellation itself, before the next attempt.
    mem.gc(&[(root, size_log2)], false);
    blanks.clear();
    blanks.get_mut(size_log2, &mem);
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..4)
            .map(|shard| {
                let mem = &mem;
                let blanks = &blanks;
                scope.spawn(move || node2lanes(&mem.create_ref(shard), blanks, root, size_log2))
            })
            .collect();
        for handle in handles {
            assert_eq!(handle.join().unwrap(), Some(expected));
        }
    });

    for cells in 0.. {
        if mem.exceeds_load_factor() {
            break;
        }
        mem.find_or_create_leaf_from_u64((1 << 63) | cells);
    }
    assert_eq!(node2lanes(&mem, &blanks, root, size_log2), Some(expected));
    assert_eq!(
        node2lanes(&mem, &blanks, blanks.get(size_log2), size_log2),
        Some(0xffff)
    );
}

#[test]
fn final_merge_preserves_shared_subtrees_and_empty_roots() {
    let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
    let mut blanks = BlankNodes::new();
    let size_log2 = LEAF_SIZE_LOG2 + 8;
    let blank = blanks.get_mut(size_log2, &mem);
    let mut a = mem.find_or_create_leaf_from_u64(0x0000_0000_0000_000f);
    let mut b = mem.find_or_create_leaf_from_u64(0x0000_0000_f000_0000);
    let mut expected = mem.find_or_create_leaf_from_u64(0x0000_0000_f000_000f);
    for _ in LEAF_SIZE_LOG2..size_log2 {
        a = mem.find_or_create_node(a, a, a, a);
        b = mem.find_or_create_node(b, b, b, b);
        expected = mem.find_or_create_node(expected, expected, expected, expected);
    }
    assert_eq!(merge_universes(&mem, &blanks, (a, b), size_log2), expected);
    assert_eq!(
        merge_final_universes(&mem, &blanks, (a, b), size_log2),
        Some(expected)
    );
    assert_eq!(
        merge_final_universes(&mem, &blanks, (b, a), size_log2),
        Some(expected)
    );
    assert_eq!(
        merge_final_universes(&mem, &blanks, (a, blank), size_log2),
        Some(a)
    );
    assert_eq!(
        merge_final_universes(&mem, &blanks, (blank, b), size_log2),
        Some(b)
    );
}

fn one_slot_merge<'a>(
    mem: &'a NodeStore<u64>,
    blank_nodes: &'a BlankNodes,
) -> FinalMerge<'a> {
    FinalMerge {
        mem,
        blank_nodes,
        cache: vec![MergeCacheEntry::default()],
        hasher: ahash::RandomState::new(),
    }
}

#[test]
fn final_merge_stops_when_a_child_exhausts_capacity() {
    // Discover the public cancellation boundary without pinning sharding constants.
    let probe = NodeStore::<u64>::new(10, 1 << 10, 1);
    for cells in 0.. {
        if probe.exceeds_load_factor() {
            break;
        }
        probe.find_or_create_leaf_from_u64((1 << 63) | cells);
    }
    let last_available = probe.len() - 1;

    // An empty cache is also the fallback when its allocation fails.
    for cache_entries in [0, 1] {
        let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
        let mut blanks = BlankNodes::new();
        let size_log2 = LEAF_SIZE_LOG2 + 2;
        blanks.get_mut(size_log2, &mem);
        let mut a = mem.find_or_create_leaf_from_u64(1);
        let mut b = mem.find_or_create_leaf_from_u64(2);
        for _ in LEAF_SIZE_LOG2..size_log2 {
            a = mem.find_or_create_node(a, a, a, a);
            b = mem.find_or_create_node(b, b, b, b);
        }
        for cells in 0.. {
            if mem.len() == last_available {
                break;
            }
            mem.find_or_create_leaf_from_u64((1 << 63) | cells);
        }
        assert!(!mem.exceeds_load_factor());
        let mut merge = FinalMerge {
            mem: &mem,
            blank_nodes: &blanks,
            cache: vec![MergeCacheEntry::default(); cache_entries],
            hasher: ahash::RandomState::new(),
        };
        assert_eq!(merge.merge((a, b), size_log2), None);
        // The leaf fit; its parent must observe the newly exhausted limit.
        assert_eq!(mem.len(), last_available + 1);
        assert!(mem.exceeds_load_factor());
    }
}

#[test]
fn final_merge_keeps_blank_and_cached_hits_available_at_capacity() {
    let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
    let mut blanks = BlankNodes::new();
    let size_log2 = LEAF_SIZE_LOG2 + 1;
    let blank = blanks.get_mut(size_log2, &mem);
    let a = mem.find_or_create_leaf_from_u64(1);
    let b = mem.find_or_create_leaf_from_u64(2);
    let a = mem.find_or_create_node(a, a, a, a);
    let b = mem.find_or_create_node(b, b, b, b);
    let mut merge = one_slot_merge(&mem, &blanks);
    let result = merge.merge((a, b), size_log2).unwrap();
    for cells in 0.. {
        if mem.exceeds_load_factor() {
            break;
        }
        mem.find_or_create_leaf_from_u64((1 << 63) | cells);
    }
    let full_len = mem.len();
    assert_eq!(merge.merge((a, b), size_log2), Some(result));
    assert_eq!(merge_final_universes(&mem, &blanks, (a, blank), size_log2), Some(a));
    assert_eq!(merge_final_universes(&mem, &blanks, (blank, b), size_log2), Some(b));
    assert_eq!(mem.len(), full_len);
}

#[test]
fn final_merge_collisions_preserve_distinct_repeated_pairs() {
    let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
    let mut blanks = BlankNodes::new();
    let size_log2 = LEAF_SIZE_LOG2 + 2;
    let blank = blanks.get_mut(size_log2, &mem);
    let nodes = [1, 2, 4, 8].map(|cells| {
        let leaf = mem.find_or_create_leaf_from_u64(cells);
        mem.find_or_create_node(leaf, leaf, leaf, leaf)
    });
    let a = mem.find_or_create_node(nodes[0], nodes[1], nodes[0], nodes[1]);
    let b = mem.find_or_create_node(nodes[2], nodes[3], nodes[2], nodes[3]);
    let mut merge = one_slot_merge(&mem, &blanks);
    for pair in [(a, b), (b, a), (a, b), (a, blank), (blank, b)] {
        assert_eq!(
            merge.merge(pair, size_log2),
            Some(merge_universes(&mem, &blanks, pair, size_log2))
        );
    }
    for pair in [
        (nodes[0], nodes[2]),
        (nodes[1], nodes[3]),
        (nodes[0], nodes[2]),
    ] {
        assert_eq!(
            merge.merge(pair, size_log2 - 1),
            Some(merge_universes(&mem, &blanks, pair, size_log2 - 1))
        );
    }
}

#[test]
#[should_panic(expected = "universes overlap")]
fn final_merge_collision_does_not_hide_overlap() {
    let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
    let mut blanks = BlankNodes::new();
    let size_log2 = LEAF_SIZE_LOG2 + 1;
    blanks.get_mut(size_log2, &mem);
    let a = mem.find_or_create_leaf_from_u64(1);
    let b = mem.find_or_create_leaf_from_u64(2);
    let a = mem.find_or_create_node(a, a, a, a);
    let b = mem.find_or_create_node(b, b, b, b);
    let mut merge = one_slot_merge(&mem, &blanks);
    assert_eq!(
        merge.merge((a, b), size_log2),
        Some(merge_universes(&mem, &blanks, (a, b), size_log2))
    );
    merge.merge((a, a), size_log2);
}

#[test]
#[should_panic(expected = "universes overlap")]
fn final_merge_rejects_overlapping_shared_subtrees() {
    let mem = NodeStore::<u64>::new(10, 1 << 10, 1);
    let mut blanks = BlankNodes::new();
    let size_log2 = LEAF_SIZE_LOG2 + 3;
    blanks.get_mut(size_log2, &mem);
    let mut root = mem.find_or_create_leaf_from_u64(1);
    for _ in LEAF_SIZE_LOG2..size_log2 {
        root = mem.find_or_create_node(root, root, root, root);
    }
    merge_final_universes(&mem, &blanks, (root, root), size_log2);
}
