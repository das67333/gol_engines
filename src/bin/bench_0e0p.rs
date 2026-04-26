use gol_engines::*;
use num_bigint::BigInt;
use std::{thread, time::Instant};

const POP_REF: u64 = 93_235_805;

struct EngineConfig {
    name: &'static str,
    mem_mib: u32,
    gens_log2: u32,
}

const HASHLIFE_CFG: EngineConfig = EngineConfig {
    name: "HashLife",
    mem_mib: 20 * 1024,
    gens_log2: 12,
};

const STREAMLIFE_CFG: EngineConfig = EngineConfig {
    name: "StreamLife",
    mem_mib: 20 * 1024,
    gens_log2: 18,
};

fn power_of_two_threads(cap: usize) -> Vec<usize> {
    let mut v = Vec::new();
    let mut t = 8;
    while t <= cap {
        v.push(t);
        t *= 2;
    }
    v
}

fn banner(cfg: &EngineConfig, threads: usize) {
    println!(
        "\n========== {} threads={} mem={}GiB gens_log2={} ==========",
        cfg.name,
        threads,
        cfg.mem_mib / 1024,
        cfg.gens_log2,
    );
}

fn run_hashlife(cfg: &EngineConfig, threads: usize, pattern: &Pattern) {
    banner(cfg, threads);

    let t0 = Instant::now();
    let mut engine = HashLifeEngine::new(cfg.mem_mib, threads);
    println!("Time spent on initializing engine: {:?}", t0.elapsed());

    let t1 = Instant::now();
    engine.load_pattern(pattern, Topology::Unbounded).unwrap();
    println!("Time spent on loading pattern: {:?}", t1.elapsed());

    let t2 = Instant::now();
    engine.update(cfg.gens_log2).unwrap();
    println!(
        "Time on updating pattern by 2^{} generations: {:?}",
        cfg.gens_log2,
        t2.elapsed()
    );

    let st = engine.current_state();
    println!("Population: {}", st.population());
    println!("Hash: 0x{:016x}", st.hash());
}

fn run_streamlife(cfg: &EngineConfig, threads: usize, pattern: &Pattern) {
    banner(cfg, threads);

    let t0 = Instant::now();
    let mut engine = StreamLifeEngine::new(cfg.mem_mib, threads);
    println!("Time spent on initializing engine: {:?}", t0.elapsed());

    let t1 = Instant::now();
    engine.load_pattern(pattern, Topology::Unbounded).unwrap();
    println!("Time spent on loading pattern: {:?}", t1.elapsed());

    let t2 = Instant::now();
    engine.update(cfg.gens_log2).unwrap();
    println!(
        "Time on updating pattern by 2^{} generations: {:?}",
        cfg.gens_log2,
        t2.elapsed()
    );

    let st = engine.current_state();
    println!("Population: {}", st.population());
    println!("Hash: 0x{:016x}", st.hash());
}

fn main() {
    let cores = thread::available_parallelism().map(|n| n.get()).unwrap();
    let threads_list = power_of_two_threads(cores);
    println!("Detected {cores} cores; sweeping power-of-two thread counts: {threads_list:?}");

    let pattern = Pattern::from_file("res/very_large_patterns/0e0p-metaglider.mc.gz").unwrap();
    assert_eq!(pattern.population(), BigInt::from(POP_REF));

    for &threads in &threads_list {
        run_hashlife(&HASHLIFE_CFG, threads, &pattern);
    }

    for &threads in &threads_list {
        run_streamlife(&STREAMLIFE_CFG, threads, &pattern);
    }
}
