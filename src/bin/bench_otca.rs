use gol_engines::*;
use num_bigint::BigInt;

fn main() {
    let timer = std::time::Instant::now();

    let top_pattern = Pattern::from_format(
        PatternFormat::PackedCells,
        &[0b010, 0b100, 0b111, 0, 0, 0, 0, 0],
    )
    .unwrap();
    let otca_off = Pattern::from_format(
        PatternFormat::CompressedMacrocell,
        &std::fs::read("../res/otca_0.mc.gz").unwrap(),
    )
    .unwrap();
    let otca_on = Pattern::from_format(
        PatternFormat::CompressedMacrocell,
        &std::fs::read("../res/otca_1.mc.gz").unwrap(),
    )
    .unwrap();
    let pattern = top_pattern.metafy(&[otca_off, otca_on], 2).unwrap();
    let mut engine = HashLifeEngineSync::new(4 << 10);
    engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
    println!("Time on building field: {:?}", timer.elapsed());

    let timer = std::time::Instant::now();
    let generations_log2 = 23;
    engine.update(generations_log2).unwrap();
    let updated = engine.current_state();
    println!("Time on big update: {:?}", timer.elapsed());
    assert_eq!(updated.population(), BigInt::from(6_094_494_746_384u64));
    assert_eq!(updated.hash(), 0xf35ef0ba0c9db279);
}
