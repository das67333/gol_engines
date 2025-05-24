mod metafy;
mod stats;
mod update;
mod util;

use clap::{Parser, Subcommand};
use metafy::{run_metafy, MetafyArgs};
use stats::{run_stats, StatsArgs};
use update::{run_update, UpdateArgs};

#[derive(Parser, Debug)]
#[command(version, about)]
struct CLIParser {
    #[command(subcommand)]
    action: Action,
}

#[derive(Subcommand, Debug)]
enum Action {
    /// Run the simulation using high-performance implementations of the update algorithms
    Update(UpdateArgs),
    /// Replace every basic cell with a corresponding metacell (see https://conwaylife.com/wiki/Unit_cell) and repeat it k times
    Metafy(MetafyArgs),
    /// Compute pattern's hash, population and nodes distribution
    Stats(StatsArgs),
}

fn main() {
    let args = CLIParser::parse();

    match args.action {
        Action::Update(args) => run_update(args),
        Action::Metafy(args) => run_metafy(args),
        Action::Stats(args) => run_stats(args),
    }
}
