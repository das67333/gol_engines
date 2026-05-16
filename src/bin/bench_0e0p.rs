use gol_engines::*;
use num_bigint::BigInt;

const POP_REF: u64 = 93_235_805;
const REPS: usize = 1;

struct EngineConfig {
    mem_mib: u32,
    gens_log2: u32,
}

const HASHLIFE_CFG: EngineConfig = EngineConfig {
    mem_mib: 20 * 1024,
    gens_log2: 12,
};

const STREAMLIFE_CFG: EngineConfig = EngineConfig {
    mem_mib: 20 * 1024,
    gens_log2: 18,
};

fn run_bench<E: GoLEngine>(name: &str, cfg: &EngineConfig, threads: usize, pattern: &Pattern) {
    let mut engine = E::new(cfg.mem_mib, threads);
    engine.load_pattern(pattern, Topology::Unbounded).unwrap();
    for rep in 1..=REPS {
        println!(
            "\n========== {} threads={} mem={}GiB gens_log2={} rep={}/{} ==========",
            name,
            threads,
            cfg.mem_mib / 1024,
            cfg.gens_log2,
            rep,
            REPS
        );
        engine.update(cfg.gens_log2).unwrap();
        let st = engine.current_state();
        println!(
            "Population: {}  Hash: 0x{:016x}",
            st.population(),
            st.hash()
        );
        engine.run_gc();
    }
}

fn main() {
    let threads_list = [6];

    let pattern = Pattern::from_file("res/very_large_patterns/0e0p-metaglider.mc.gz").unwrap();
    assert_eq!(pattern.population(), BigInt::from(POP_REF));

    for &threads in &threads_list {
        run_bench::<HashLifeEngine>("HashLife", &HASHLIFE_CFG, threads, &pattern);
    }

    for &threads in &threads_list {
        run_bench::<StreamLifeEngine>("StreamLife", &STREAMLIFE_CFG, threads, &pattern);
    }
}
