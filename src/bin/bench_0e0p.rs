use gol_engines::*;
use num_bigint::BigInt;
use std::sync::atomic::*;

fn main() {
    let timer = std::time::Instant::now();
    let mut engine = StreamLifeEngineAsync::new(4 << 10);
    println!("Time spent on initializing engine: {:?}", timer.elapsed());

    let timer = std::time::Instant::now();
    let data = std::fs::read("res/very_large_patterns/0e0p-metaglider.mc.gz").unwrap();
    let pattern = Pattern::from_format(PatternFormat::CompressedMacrocell, &data).unwrap();
    engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
    assert_eq!(pattern.population(), BigInt::from(93_235_805));
    println!("Time spent on loading pattern: {:?}", timer.elapsed());

    let timer = std::time::Instant::now();
    let gens_log2 = 15;
    engine.update(gens_log2).unwrap();
    println!(
        "Time on updating pattern for 2^{} generations: {:?}",
        gens_log2,
        timer.elapsed()
    );

    let updated = engine.current_state();
    println!(
        "TASKS_SPAWN_COUNT: {}",
        TASKS_SPAWN_COUNT.swap(0, Ordering::Relaxed)
    );
    println!("Population: {}", updated.population());
    println!("Hash: 0x{:016x}", updated.hash());
    assert_eq!(updated.hash(), 0x6cf9bfab4d7fdaef);
}
