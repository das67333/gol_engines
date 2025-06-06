use crate::util::{local_time, print_population};
use clap::{Args, ValueEnum};
use gol_engines::{
    GoLEngine, HashLifeEngineAsync, HashLifeEngineSync, Pattern, StreamLifeEngineAsync,
    StreamLifeEngineSync, WORKER_THREADS,
};
use num_bigint::BigInt;

#[derive(Args, Debug)]
pub(super) struct UpdateArgs {
    /// Path to the file containing the pattern; supports .rle, .mc and .mc.gz formats
    pattern: String,

    /// Path to the file where the resulting pattern will be saved
    #[arg(short, long)]
    output: String,

    /// The engine to use for the simulation
    #[arg(short, long, value_enum, default_value_t = Engine::Hashlife)]
    engine: Engine,

    /// Maximum memory (in GiB) allocated to the hash tables;
    /// all other usage is typically negligible
    #[arg(short, long)]
    mem_limit_gib: u32,

    /// The number of worker threads to use for the update;
    /// ignored for single-threaded engines
    #[arg(short, long, default_value_t = 1)]
    workers: u32,

    /// The pattern will be updated by 2^gens_log2 generations
    #[arg(short, long)]
    gens_log2: u32,

    /// How many generations to update at once, uses `gens_log2` by default
    #[arg(short, long)]
    step_log2: Option<u32>,

    /// The topology of the pattern
    #[arg(short, long, value_enum, default_value_t = Topology::Unbounded)]
    topology: Topology,

    /// Count population of the resulting pattern
    #[arg(short, long)]
    population: bool,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, ValueEnum)]
enum Engine {
    /// Parallel implementation of HashLife
    Hashlife,
    /// Single-threaded implementation of HashLife
    HashlifeSt,
    /// Parallel implementation of StreamLife
    Streamlife,
    /// Single-threaded implementation of StreamLife
    StreamlifeSt,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, ValueEnum)]
enum Topology {
    /// The pattern is unbounded in all directions
    Unbounded,
    /// Opposite bounds of the field are stitched together
    Torus,
}

pub(super) fn run_update(args: UpdateArgs) {
    let mut step_log2 = args.step_log2.unwrap_or(args.gens_log2);
    assert!(
        step_log2 <= args.gens_log2,
        "step_log2 cannot exceed gens_log2"
    );
    assert!(args.workers > 0, "Number of workers must be greater than 0");
    assert!(
        args.mem_limit_gib > 0,
        "Memory limit must be greater than 0"
    );

    WORKER_THREADS.store(args.workers, std::sync::atomic::Ordering::Relaxed);
    let mem_limit_mib = args.mem_limit_gib.saturating_mul(1024);
    let topology = match args.topology {
        Topology::Unbounded => gol_engines::Topology::Unbounded,
        Topology::Torus => gol_engines::Topology::Torus,
    };

    let timer = std::time::Instant::now();
    let mut engine: Box<dyn GoLEngine> = match args.engine {
        Engine::Hashlife => Box::new(HashLifeEngineAsync::new(mem_limit_mib)),
        Engine::HashlifeSt => Box::new(HashLifeEngineSync::new(mem_limit_mib)),
        Engine::Streamlife => Box::new(StreamLifeEngineAsync::new(mem_limit_mib)),
        Engine::StreamlifeSt => Box::new(StreamLifeEngineSync::new(mem_limit_mib)),
    };
    println!(
        "Initialized engine in {:.1} secs",
        timer.elapsed().as_secs_f64()
    );

    let timer = std::time::Instant::now();
    let pattern = Pattern::from_file(&args.pattern).unwrap();
    engine.load_pattern(&pattern, topology).unwrap();
    println!(
        "Loaded pattern in {:.1} secs",
        timer.elapsed().as_secs_f64()
    );

    let timer = std::time::Instant::now();
    let mut step = BigInt::from(1) << step_log2;
    let gens_total = BigInt::from(1) << args.gens_log2;
    let mut gens_left = gens_total.clone();
    let mut gc_can_help = false;
    loop {
        match engine.update(step_log2) {
            Ok(_) => {
                gens_left -= &step;
                if gens_left == BigInt::ZERO {
                    break;
                }
                println!(
                    "{}  Updated by {} out of {} generations",
                    local_time(),
                    &gens_total - &gens_left,
                    &gens_total
                );
                gc_can_help = true;
            }
            Err(_) => {
                if gc_can_help {
                    println!("{}  Overfilled hashtables, running GC", local_time());
                    engine.run_gc();
                    gc_can_help = false;
                } else {
                    let new_step_log2 = step_log2.checked_sub(2).unwrap();
                    println!(
                        "{}  Overfilled hashtables, reducing step_log2 from {} to {}",
                        local_time(),
                        step_log2,
                        new_step_log2
                    );
                    step_log2 = new_step_log2;
                    step = BigInt::from(1) << step_log2;
                }
            }
        }
    }
    println!(
        "Updated pattern by 2^{} generations in {:.1} secs",
        args.gens_log2,
        timer.elapsed().as_secs_f64()
    );

    let updated = engine.current_state();
    if args.population {
        print_population(&updated);
    }
    updated.to_file(&args.output).unwrap();
}
