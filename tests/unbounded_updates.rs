use gol_engines::{GoLEngine, HashLifeEngine, Pattern, PatternFormat, StreamLifeEngine, Topology};
use std::collections::{BTreeMap, BTreeSet};

type Cells = BTreeSet<(i64, i64)>;

fn cells(pattern: &Pattern, shift: [i64; 2]) -> Cells {
    let side = 1usize << pattern.get_size_log2();
    let packed = pattern.to_format(PatternFormat::PackedCells).unwrap();
    let mut result = Cells::new();
    for y in 0..side {
        for x in 0..side {
            if packed[(x + y * side) / 8] & (1 << (x % 8)) != 0 {
                result.insert((x as i64 - shift[0], y as i64 - shift[1]));
            }
        }
    }
    result
}

fn advance(cells: &Cells) -> Cells {
    let mut neighbors = BTreeMap::<_, u8>::new();
    for &(x, y) in cells {
        for dy in -1..=1 {
            for dx in -1..=1 {
                if dx != 0 || dy != 0 {
                    *neighbors.entry((x + dx, y + dy)).or_default() += 1;
                }
            }
        }
    }
    neighbors
        .into_iter()
        .filter_map(|(cell, count)| {
            (count == 3 || (count == 2 && cells.contains(&cell))).then_some(cell)
        })
        .collect()
}

#[test]
fn unbounded_updates_preserve_growth_across_the_initial_boundary() {
    let glider = Pattern::from_format(
        PatternFormat::RLE,
        b"x = 16, y = 16, rule = B3/S23\n13$14bo$15bo$13b3o!",
    )
    .unwrap();
    for pattern in [glider, Pattern::random(5, Some(42)).unwrap()] {
        for workers in [1, 4] {
            for step in [0, 3, 5] {
                let engines: Vec<Box<dyn GoLEngine>> = vec![
                    Box::new(HashLifeEngine::new(64, workers)),
                    Box::new(StreamLifeEngine::new(64, workers)),
                ];
                for mut engine in engines {
                    engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
                    let mut expected = cells(&pattern, [0, 0]);
                    let mut shift = [0i64, 0];
                    for _ in 0..(32 >> step) {
                        for _ in 0..(1 << step) {
                            expected = advance(&expected);
                        }
                        let delta = engine.update(step).unwrap();
                        for axis in 0..2 {
                            shift[axis] += i64::try_from(&delta[axis]).unwrap();
                        }
                        assert_eq!(
                            cells(&engine.current_state(), shift),
                            expected,
                            "workers={workers}, step={step}"
                        );
                    }
                }
            }
        }
    }
}
