use crate::util::print_population;
use clap::Args;
use gol_engines::Pattern;
use gol_engines::{GoLEngine, HashLifeEngineSmall, Topology};

#[derive(Args, Debug)]
pub(super) struct StatsArgs {
    /// Path to the file containing the pattern; supports .rle, .mc and .mc.gz formats
    pattern: String,
}

pub(super) fn run_stats(args: StatsArgs) {
    let timer = std::time::Instant::now();
    let mut pattern = Pattern::from_file(&args.pattern).unwrap();
    pattern.expand(3); // expand to at least leaf size
    println!("Hash: 0x{:016x}", pattern.hash());
    print_population(&pattern);
    let mut engine = HashLifeEngineSmall::new(0);
    engine.load_pattern(&pattern, Topology::Unbounded).unwrap();
    print!("{}", engine.sizes_distribution());
    println!(
        "Computed stats in {:.1} secs",
        timer.elapsed().as_secs_f64()
    );
}
