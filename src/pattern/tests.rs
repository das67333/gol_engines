use super::*;
const SEED: u64 = 42;
// for simple patterns
const HUGE_SIZE_LOG2_LIMIT: SizeLog2 = 300;
// for conversions from/to packed cells
const MEDIUM_SIZE_LOG2_LIMIT: SizeLog2 = 10;

fn repeat_leaf(leaf: u64, size_log2: SizeLog2) -> Pattern {
    let mut kiv = KIVMap::new();
    let cells = if size_log2 >= 3 {
        leaf
    } else {
        let mut x = leaf.to_le_bytes();
        for i in 0..1 << size_log2 {
            x[i] &= ((1u32 << (1 << size_log2)) - 1) as u8;
        }
        for i in (1 << size_log2)..8 {
            x[i] = 0;
        }
        u64::from_le_bytes(x)
    };
    let mut node = kiv.find_or_create_node(PatternNode::Leaf(cells));
    for _ in 3..size_log2 {
        node = kiv.find_or_create_node(PatternNode::Node {
            nw: node,
            ne: node,
            sw: node,
            se: node,
        });
    }
    Pattern {
        root: node,
        size_log2,
        kiv,
    }
}

#[test]
fn test_population() {
    for size_log2 in 0..HUGE_SIZE_LOG2_LIMIT {
        for (leaf, expected) in [
            (0, BigInt::ZERO),
            (1, BigInt::from(1u64) << (size_log2.max(3) - 3) * 2),
            (u64::MAX, BigInt::from(1u64) << (size_log2 * 2)),
        ] {
            assert_eq!(
                repeat_leaf(leaf, size_log2).population(),
                expected,
                "leaf={leaf}, size={size_log2}"
            );
        }
    }
}

#[test]
fn test_metafy_glider() {
    // Create a glider pattern (4x4)
    let glider = Pattern::from_rle(b"x = 3, y = 3, rule = B3/S23\nbo$2bo$3o!").unwrap();

    // Create metacells where ON is a smaller glider and OFF is empty
    let off_metacell = repeat_leaf(0, 3); // All dead cells
    let on_metacell = Pattern::from_packed_cells(&[0b00100000, 0b00010000, 0b01110000, 0, 0, 0, 0, 0]).unwrap();

    // Metafy with level 1
    let metafied = glider.metafy([&off_metacell, &on_metacell], 1).unwrap();

    // The metafied pattern should have 5 gliders (one for each ON cell in the original glider)
    assert_eq!(metafied.size_log2, 5);
    assert_eq!(metafied.population(), BigInt::from(5 * 5)); // 5 gliders with 5 cells each
}

#[test]
fn test_metafy_simple() {
    // Create a simple pattern (2x2)
    let pattern = Pattern::from_packed_cells(&[0b11, 0b10]).unwrap();

    // Create simple metacells (8x8)
    let off_metacell = repeat_leaf(1, 3); // 1 alive cell
    let on_metacell = repeat_leaf(u64::MAX, 3); // All alive cells

    let mut off_population = BigInt::from(0);
    let mut on_population = BigInt::from(1);
    let mut level = 0;
    let size_log2 = |level: u32| 1 + level * 3;
    while size_log2(level) < HUGE_SIZE_LOG2_LIMIT {
        let metafied = pattern.metafy([&off_metacell, &on_metacell], level).unwrap();

        assert_eq!(metafied.size_log2, size_log2(level));
        assert_eq!(
            metafied.population(),
            off_population.clone() + on_population.clone() * 3
        );
        (off_population, on_population) = (off_population * 63 + on_population.clone(), on_population * 64);
        level += 1;
    }
}

#[test]
fn test_metafy_random() {
    for pattern_size_log2 in 0..6 {
        let pattern_total_count = BigInt::from(1) << pattern_size_log2 * 2;
        let pattern = Pattern::random(pattern_size_log2, Some(SEED)).unwrap();
        for metacell_size_log2 in 3..6 {
            let metacell_total_count = BigInt::from(1) << metacell_size_log2 * 2;
            let off_metacell = Pattern::random(metacell_size_log2, Some(SEED + 1)).unwrap();
            let on_metacell = Pattern::random(metacell_size_log2, Some(SEED + 2)).unwrap();
            let metacells = [&off_metacell, &on_metacell];

            let mut populations = [BigInt::from(0), BigInt::from(1)];
            let mut total_count = BigInt::from(1);
            for level in 0..10 {
                let metafied = pattern.metafy(metacells, level).unwrap();

                assert_eq!(metafied.size_log2, pattern_size_log2 + metacell_size_log2 * level);
                assert_eq!(
                    metafied.population(),
                    pattern.population() * &populations[1]
                        + (&pattern_total_count - pattern.population()) * &populations[0]
                );
                populations = [
                    &populations[0] * metacells[1].population()
                        + (&total_count - &populations[0]) * &metacells[0].population(),
                    &populations[1] * metacells[1].population()
                        + (&total_count - &populations[1]) * &metacells[0].population(),
                ];
                total_count *= &metacell_total_count;
            }
        }
    }
}

#[test]
fn test_expand() {
    let mut pattern = repeat_leaf(1, 0);
    for size_log2 in 0..HUGE_SIZE_LOG2_LIMIT {
        pattern.expand(size_log2);
        assert_eq!(pattern.size_log2, size_log2);
        assert_eq!(pattern.population(), BigInt::from(1));
    }
}

fn assert_roundtrip(pattern: &Pattern, format: PatternFormat) {
    let data = pattern.to_format(format).unwrap();
    let restored = Pattern::from_format(format, &data).unwrap();
    let expected_size = match format {
        PatternFormat::Macrocell | PatternFormat::CompressedMacrocell => pattern.size_log2.max(3),
        _ => pattern.size_log2,
    };
    assert_eq!(
        restored.size_log2, expected_size,
        "format={format:?}, size={}",
        pattern.size_log2
    );
    assert_eq!(
        restored.population(),
        pattern.population(),
        "format={format:?}, size={}",
        pattern.size_log2
    );
    assert_eq!(
        restored.hash(),
        pattern.hash(),
        "format={format:?}, size={}",
        pattern.size_log2
    );
}

#[test]
fn test_repeated_leaf_roundtrips() {
    for size_log2 in 0..HUGE_SIZE_LOG2_LIMIT {
        for leaf in [0, 1, u64::MAX] {
            let pattern = repeat_leaf(leaf, size_log2);
            if size_log2 < MEDIUM_SIZE_LOG2_LIMIT {
                assert_roundtrip(&pattern, PatternFormat::PackedCells);
            }
            if leaf != 0 {
                assert_roundtrip(&pattern, PatternFormat::Macrocell);
            }
        }
    }
}

#[test]
fn test_random_format_roundtrips() {
    for size_log2 in 0..MEDIUM_SIZE_LOG2_LIMIT {
        let pattern = Pattern::random(size_log2, Some(SEED)).unwrap();
        for format in [
            PatternFormat::PackedCells,
            PatternFormat::Macrocell,
            PatternFormat::CompressedMacrocell,
            PatternFormat::RLE,
        ] {
            assert_roundtrip(&pattern, format);
        }
    }
}

#[test]
fn test_conversions_glider() {
    let packed = Pattern::from_packed_cells(&[0b010, 0b100, 0b111, 0]).unwrap();
    let rle = Pattern::from_rle(b"x = 3, y = 3, rule = B3/S23\nbo$2bo$3o!").unwrap();
    let macrocell = Pattern::from_macrocell(b"[M2]\n#R B3/S23\n.*.$..*$***$").unwrap();

    assert_eq!(packed.hash(), rle.hash());
    assert_eq!(packed.hash(), macrocell.hash());
}

#[test]
fn blank_macrocell_roundtrip_preserves_field_size() {
    for size in [3, 4, 32, 300] {
        let pattern = repeat_leaf(0, size);
        for format in [PatternFormat::Macrocell, PatternFormat::CompressedMacrocell] {
            let restored = Pattern::from_format(format, &pattern.to_format(format).unwrap()).unwrap();
            assert_eq!(restored.get_size_log2(), size);
            assert_eq!(restored.population(), BigInt::ZERO);
        }
    }
}
