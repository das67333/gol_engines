use gol_engines::*;
use num_bigint::BigInt;
use std::sync::atomic::*;

fn main() {
    let timer = std::time::Instant::now();
    let mut engine = StreamLifeEngineAsync::new(4 << 10);
    println!("Time spent on initializing engine: {:?}", timer.elapsed());
    let pattern = Pattern::from_file("res/very_large_patterns/0e0p-metaglider.mc.gz").unwrap();

    for workers in 8..=8 {
        // [2, 4, 8, 12, 16, 20, 24, 32, 40, 48] {
        WORKER_THREADS.store(workers, Ordering::Relaxed);
        println!("Using {} worker threads", workers);

        let timer = std::time::Instant::now();
        engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
        assert_eq!(pattern.population(), BigInt::from(93_235_805));
        println!("Time spent on loading pattern: {:?}", timer.elapsed());

        let timer = std::time::Instant::now();
        let gens_log2 = 10;
        engine.update(gens_log2).unwrap();
        println!(
            "Time on updating pattern by 2^{} generations: {:?}",
            gens_log2,
            timer.elapsed()
        );

        let updated = engine.current_state();
        println!(
            "TASKS_SPAWNED_COUNT: {}",
            TASKS_SPAWNED_COUNT.swap(0, Ordering::Relaxed)
        );
        println!("Population: {}", updated.population());
        println!("Hash: 0x{:016x}", updated.hash());
        // assert_eq!(updated.hash(), 0x6cf9bfab4d7fdaef);
    }
}
