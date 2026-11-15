use crate::{
    checkpoint::{Checkpoints, atomic_write},
    util::{local_time, print_population},
};
use anyhow::{Context, Result, ensure};
use clap::{Args, ValueEnum};
use gol_engines::{GoLEngine, HashLifeEngine, Pattern, PatternFormat, StreamLifeEngine, UpdateCancelled};
use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use std::{
    path::{Path, PathBuf},
    time::Instant,
};

#[derive(Args, Debug)]
pub(super) struct UpdateArgs {
    /// Input pattern (.rle, .mc or .mc.gz) with a field of at least 16x16 cells
    pattern: PathBuf,
    #[command(flatten)]
    settings: Settings,
    /// The pattern will be updated by 2^gens_log2 generations
    #[arg(short, long)]
    gens_log2: u32,
    /// How many generations to update at once, uses gens_log2 by default
    #[arg(short, long)]
    step_log2: Option<u32>,
    /// Save a resumable checkpoint after each completed step
    #[arg(long)]
    checkpoint_dir: Option<PathBuf>,
}

#[derive(Args, Debug)]
pub(super) struct ResumeArgs {
    /// Directory created by update --checkpoint-dir
    directory: PathBuf,
    /// Override the saved memory budget (GiB)
    #[arg(short, long)]
    mem_limit_gib: Option<u32>,
    /// Override the saved worker count
    #[arg(short, long)]
    workers: Option<usize>,
}

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub(super) struct Settings {
    /// Path to the file where the resulting pattern will be saved
    #[arg(short, long)]
    output: PathBuf,
    /// The engine to use for the simulation
    #[arg(short, long, value_enum, default_value_t = Engine::Hashlife)]
    engine: Engine,
    /// Memory budget for hash tables in GiB (not a hard RSS limit)
    #[arg(short, long)]
    mem_limit_gib: u32,
    /// Number of worker threads
    #[arg(short, long, default_value_t = 1)]
    workers: usize,
    /// The topology of the pattern
    #[arg(short, long, value_enum, default_value_t = Topology::Unbounded)]
    topology: Topology,
    /// Count population of the resulting pattern
    #[arg(short, long)]
    population: bool,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, ValueEnum, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Engine {
    Hashlife,
    Streamlife,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, ValueEnum, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Topology {
    Unbounded,
    Torus,
}

#[derive(Clone, Serialize, Deserialize)]
pub(super) struct Progress {
    #[serde(with = "decimal")]
    generation: BigInt,
    #[serde(with = "decimal")]
    target: BigInt,
    step_log2: u32,
    elapsed_seconds: f64,
}

impl Settings {
    pub(super) fn validate(&self) -> Result<()> {
        ensure!(self.workers > 0, "Number of workers must be greater than 0");
        ensure!(self.mem_limit_gib > 0, "Memory limit must be greater than 0");
        Ok(())
    }
}

impl Progress {
    fn new(gens_log2: u32, step_log2: u32) -> Self {
        Self {
            generation: BigInt::ZERO,
            target: BigInt::from(1) << gens_log2,
            step_log2,
            elapsed_seconds: 0.0,
        }
    }

    pub(super) fn validate(&self) -> Result<()> {
        ensure!(
            self.generation >= BigInt::ZERO && self.generation <= self.target,
            "Invalid checkpoint generation"
        );
        ensure!(
            self.target > BigInt::ZERO && u64::from(self.step_log2) < self.target.bits(),
            "Invalid checkpoint step"
        );
        ensure!(
            self.elapsed_seconds.is_finite() && self.elapsed_seconds >= 0.0,
            "Invalid checkpoint elapsed time"
        );
        Ok(())
    }

    fn next_step(&self) -> Option<u32> {
        let remaining = &self.target - &self.generation;
        (remaining > BigInt::ZERO).then(|| self.step_log2.min((remaining.bits() - 1) as u32))
    }
}

pub(super) fn run_update(mut args: UpdateArgs) -> Result<()> {
    let step_log2 = args.step_log2.unwrap_or(args.gens_log2);
    ensure!(step_log2 <= args.gens_log2, "step_log2 cannot exceed gens_log2");
    args.settings.validate()?;
    args.settings.output = std::path::absolute(&args.settings.output)?;
    let pattern = Pattern::from_file(&args.pattern)?;
    let mut checkpoints = args.checkpoint_dir.as_deref().map(Checkpoints::create).transpose()?;
    let progress = Progress::new(args.gens_log2, step_log2);
    if let Some(store) = &mut checkpoints {
        store.save(&args.settings, &progress, &pattern)?;
    }
    run(args.settings, progress, pattern, checkpoints)
}

pub(super) fn run_resume(args: ResumeArgs) -> Result<()> {
    let (store, mut settings, progress, pattern) = Checkpoints::open(&args.directory)?;
    if let Some(memory) = args.mem_limit_gib {
        settings.mem_limit_gib = memory;
    }
    if let Some(workers) = args.workers {
        settings.workers = workers;
    }
    settings.validate()?;
    run(settings, progress, pattern, Some(store))
}

fn run(
    settings: Settings,
    mut progress: Progress,
    pattern: Pattern,
    mut checkpoints: Option<Checkpoints>,
) -> Result<()> {
    let timer = Instant::now();
    let elapsed_before = progress.elapsed_seconds;
    let memory = settings.mem_limit_gib.saturating_mul(1024);
    let mut engine: Box<dyn GoLEngine> = match settings.engine {
        Engine::Hashlife => Box::new(HashLifeEngine::new(memory, settings.workers)),
        Engine::Streamlife => Box::new(StreamLifeEngine::new(memory, settings.workers)),
    };
    let cancellation = engine
        .cancellation_token()
        .expect("Both CLI engines support cancellation");
    let signal = cancellation.clone();
    let has_checkpoints = checkpoints.is_some();
    let mut interrupted = false;
    ctrlc::set_handler(move || {
        if interrupted {
            std::process::exit(130);
        }
        interrupted = true;
        signal.cancel();
        eprintln!("Cancelling the unfinished step. Press Ctrl+C again to exit immediately.");
        if has_checkpoints {
            eprintln!("The last saved checkpoint remains usable with resume.");
        }
    })?;
    let topology = match settings.topology {
        Topology::Unbounded => gol_engines::Topology::Unbounded,
        Topology::Torus => gol_engines::Topology::Torus,
    };
    engine.load_pattern(&pattern, topology)?;
    drop(pattern);
    println!(
        "Initialized and loaded in {:.1} secs; generation {}/{}",
        timer.elapsed().as_secs_f64(),
        progress.generation,
        progress.target
    );
    let mut can_retry = false;
    while let Some(mut step) = progress.next_step() {
        let started = Instant::now();
        if let Err(error) = advance(&mut step, &mut can_retry, |s| engine.update(s)) {
            eprintln!(
                "Stopped at generation {}/{}; the unfinished step was discarded",
                progress.generation, progress.target
            );
            return Err(error);
        }
        progress.generation += BigInt::from(1) << step;
        progress.step_log2 = step;
        progress.elapsed_seconds = elapsed_before + timer.elapsed().as_secs_f64();
        if let Some(store) = &mut checkpoints {
            store
                .save(&settings, &progress, &engine.current_state())
                .context("Failed to save checkpoint; the previous checkpoint is intact")?;
        }
        println!(
            "{}  Generation {}/{}; S{}; step {:.2}s; elapsed {:.1}s{}",
            local_time(),
            progress.generation,
            progress.target,
            step,
            started.elapsed().as_secs_f64(),
            progress.elapsed_seconds,
            if checkpoints.is_some() {
                "; checkpoint saved"
            } else {
                ""
            }
        );
        if cancellation.is_cancelled() {
            return Err(UpdateCancelled.into());
        }
    }
    let updated = engine.current_state();
    if settings.population {
        print_population(&updated);
    }
    save_output(&settings.output, &updated)?;
    println!(
        "Saved {} at generation {}",
        settings.output.display(),
        progress.generation
    );
    Ok(())
}

fn save_output(path: &Path, pattern: &Pattern) -> Result<()> {
    let format = PatternFormat::from_path(path)?;
    atomic_write(path, &pattern.to_format(format)?)
}

fn advance(
    step_log2: &mut u32,
    can_retry: &mut bool,
    mut update: impl FnMut(u32) -> Result<[BigInt; 2]>,
) -> Result<()> {
    loop {
        match update(*step_log2) {
            Ok(_) => {
                *can_retry = true;
                return Ok(());
            }
            Err(error) if error.is::<UpdateCancelled>() => return Err(error),
            Err(error) => {
                if *can_retry {
                    println!("{}  Overfilled hashtables, retrying after rollback", local_time());
                    *can_retry = false;
                } else if *step_log2 <= 1 {
                    return Err(error.context("Cannot advance at the minimum step; increase --mem-limit-gib"));
                } else {
                    println!(
                        "{}  Overfilled hashtables, reducing step_log2 from {} to {}",
                        local_time(),
                        step_log2,
                        *step_log2 - 2
                    );
                    *step_log2 -= 2;
                }
            }
        }
    }
}

mod decimal {
    use num_bigint::BigInt;
    use serde::{Deserialize, Deserializer, Serializer};
    pub(super) fn serialize<S: Serializer>(value: &BigInt, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&value.to_string())
    }
    pub(super) fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<BigInt, D::Error> {
        String::deserialize(deserializer)?
            .parse()
            .map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests;
