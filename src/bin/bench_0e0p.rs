use gol_engines::*;
use num_bigint::BigInt;
use std::sync::atomic::*;

fn main() {
    for x in 1..=96 {
        // MIN_TASK_SPAWN_SIZE_LOG2_ANOTHER.store(x, Ordering::Relaxed);
        // println!(
        //     "MIN_TASK_SPAWN_SIZE_LOG2_ANOTHER: {}",
        //     MIN_TASK_SPAWN_SIZE_LOG2_ANOTHER.load(Ordering::Relaxed)
        // );
        // let timer = std::time::Instant::now();
        let data = std::fs::read("res/very_large_patterns/0e0p-metaglider.mc.gz").unwrap();
        WORKER_THREADS.store(x, Ordering::Relaxed);

        let pattern = Pattern::from_format(PatternFormat::CompressedMacrocell, &data).unwrap();
        let mut engine = StreamLifeEngineAsync::new(4 << 10);
        engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
        assert_eq!(pattern.population(), BigInt::from(93_235_805));
        // println!("Time spent on building field: {:?}", timer.elapsed());

        let timer = std::time::Instant::now();
        engine.update(15).unwrap();
        let elapsed = timer.elapsed();
        // println!("Time on big update: {:?}", timer.elapsed());
        println!("x={} time={} ", x, elapsed.as_secs_f64());

        // let timer = std::time::Instant::now();
        // engine.run_gc();
        // println!("Time on GC: {:?}", timer.elapsed());

        let updated = engine.current_state();
        println!(
            "TASKS_SPAWN_COUNT: {}",
            TASKS_SPAWN_COUNT.load(Ordering::Relaxed)
        );
        assert_eq!(updated.population(), BigInt::from(93237495));
        assert_eq!(updated.hash(), 7852518167757708015);
        TASKS_SPAWN_COUNT.store(0, Ordering::Relaxed);
    }
}
