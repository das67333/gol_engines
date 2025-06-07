use crate::util::print_population;
use clap::Args;
use gol_engines::Pattern;

#[derive(Args, Debug)]
pub(super) struct MetafyArgs {
    /// Path to the file containing the pattern; supports .rle, .mc and .mc.gz formats
    pattern: String,

    /// Path to the file containing the off state of the metacell
    meta_0: String,

    /// Path to the file containing the on state of the metacell
    meta_1: String,

    /// The number of times to apply the metacell replacement
    #[arg(short, long, default_value_t = 1)]
    k: u32,

    /// Path to the file where the resulting pattern will be saved
    #[arg(short, long)]
    output: String,

    /// Count population of the resulting pattern
    #[arg(short, long)]
    population: bool,
}

pub(super) fn run_metafy(args: MetafyArgs) {
    let timer = std::time::Instant::now();
    let pattern = Pattern::from_file(&args.pattern).unwrap();
    let meta_0 = Pattern::from_file(&args.meta_0).unwrap();
    let meta_1 = Pattern::from_file(&args.meta_1).unwrap();
    println!(
        "Loaded patterns in {:.1} secs",
        timer.elapsed().as_secs_f64()
    );

    let timer = std::time::Instant::now();
    let metafied = pattern.metafy([&meta_0, &meta_1], args.k).unwrap();
    println!(
        "Metafied pattern in {:.1} secs",
        timer.elapsed().as_secs_f64()
    );
    if args.population {
        print_population(&metafied);
    }
    metafied.to_file(&args.output).unwrap();
}
