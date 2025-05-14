use gol_engines::*;
use num_bigint::BigInt;
use std::sync::atomic::*;

fn main() {
    for x in 15..=17 {
        // MIN_TASK_SPAWN_SIZE_LOG2.store(x, Ordering::Relaxed);
        // println!(
        //     "MIN_TASK_SPAWN_SIZE_LOG2: {}",
        //     MIN_TASK_SPAWN_SIZE_LOG2.load(Ordering::Relaxed)
        // );
        // let timer = std::time::Instant::now();
        let data = std::fs::read("../res/very_large_patterns/0e0p-metaglider.mc.gz").unwrap();
        WORKER_THREADS.store(16, Ordering::Relaxed);

        let pattern = Pattern::from_format(PatternFormat::CompressedMacrocell, &data).unwrap();
        let mut engine = StreamLifeEngineSync::new(2 << 10);
        engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
        assert_eq!(pattern.population(), BigInt::from(93_235_805));
        // println!("Time spent on building field: {:?}", timer.elapsed());

        let timer = std::time::Instant::now();
        engine.update(x).unwrap();
        let elapsed = timer.elapsed();
        // println!("Time on big update: {:?}", timer.elapsed());
        println!("x={} time={} ", x, elapsed.as_secs_f64());
        // println!("lens={:?}", engine.lens());

        // let timer = std::time::Instant::now();
        // engine.run_gc();
        // println!("Time on GC: {:?}", timer.elapsed());

        // let updated = engine.current_state();
        // println!(
        //     "TASKS_SPAWN_COUNT: {}",
        //     TASKS_SPAWN_COUNT.load(Ordering::Relaxed)
        // );
        // println!(
        //     "NODES_CREATED_COUNT: {}",
        //     NODES_CREATED_COUNT.load(Ordering::Relaxed)
        // );
        // assert_eq!(updated.population(), BigInt::from(93_236_670));
        // assert_eq!(updated.hash(), 0x5e1805e773c45a65);
        // assert_eq!(updated.population(), BigInt::from(93_237_300));
        // assert_eq!(updated.hash(), 206505887300519070);
        TASKS_SPAWN_COUNT.store(0, Ordering::Relaxed);
        NODES_CREATED_COUNT.store(0, Ordering::Relaxed);
    }
}
