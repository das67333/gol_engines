use crate::util::print_population;
use ahash::AHashSet;
use clap::Args;
use gol_engines::{Pattern, PatternNode};

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
    print_distibution(&pattern);
    println!(
        "Computed stats in {:.1} secs",
        timer.elapsed().as_secs_f64()
    );
}

fn print_distibution(pattern: &Pattern) {
    fn inner(
        idx: u32,
        size_log2: u32,
        pattern: &Pattern,
        visited: &mut AHashSet<u32>,
        distribution: &mut Vec<u32>,
    ) {
        if !visited.insert(idx) {
            return;
        }

        distribution[size_log2 as usize] += 1;
        match pattern.get_node(idx) {
            PatternNode::Leaf(_) => (),
            PatternNode::Node { nw, ne, sw, se } => {
                for &child in [nw, ne, sw, se] {
                    inner(child, size_log2 - 1, pattern, visited, distribution);
                }
            }
        }
    }

    let mut visited = AHashSet::new();
    let mut distribution = vec![0; pattern.get_size_log2() as usize + 1];
    inner(
        pattern.get_root(),
        pattern.get_size_log2(),
        pattern,
        &mut visited,
        &mut distribution,
    );

    println!("Distribution of node sizes (side lengths of the squares):");
    let nodes_total = distribution.iter().map(|&x| x as u64).sum::<u64>();
    println!("total -> {nodes_total}");
    for (i, &x) in distribution.iter().enumerate() {
        let percent = x as u64 * 100 / nodes_total;
        if percent == 0 {
            continue;
        }
        println!("2^{:<4}->{:>3}%", i, percent);
    }
}
