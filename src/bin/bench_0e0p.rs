use gol_engines::*;
use num_bigint::BigInt;
use std::sync::atomic::Ordering;

fn main() {
    let timer = std::time::Instant::now();
    let mut engine = HashLifeEngineAsync::new(5 << 10);
    println!("Time spent on initializing engine: {:?}", timer.elapsed());

    let timer = std::time::Instant::now();
    let pattern = Pattern::from_file("res/very_large_patterns/0e0p-metaglider.mc.gz").unwrap();
    // let pattern = Pattern::from_file("res/otca_0.mc.gz").unwrap();
    engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
    assert_eq!(pattern.population(), BigInt::from(93_235_805));
    println!("Time spent on loading pattern: {:?}", timer.elapsed());

    WORKER_THREADS.store(4, Ordering::Relaxed);
    let timer = std::time::Instant::now();
    let gens_log2 = 10;
    engine.update(gens_log2).unwrap();
    println!(
        "Time on updating pattern by 2^{} generations: {:?}",
        gens_log2,
        timer.elapsed()
    );

    let updated = engine.current_state();
    // println!(
    //     "TASKS_SPAWNED_COUNT: {}",
    //     TASKS_SPAWNED_COUNT.swap(0, Ordering::Relaxed)
    // );
    println!("Population: {}", updated.population());
    println!("Hash: 0x{:016x}", updated.hash());
    assert_eq!(updated.hash(), 0x5e1805e773c45a65);
}
