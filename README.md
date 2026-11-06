# GoL Engines

A Rust library and CLI for Conway's Game of Life (B3/S23), with parallel HashLife and StreamLife.

[![Crates.io](https://img.shields.io/crates/v/gol_engines.svg)](https://crates.io/crates/gol_engines)
[![License: GPL v3](https://img.shields.io/badge/license-GPLv3-blue.svg)](LICENSE)

## Engines and capabilities

| Engine | CLI name | How it works |
| --- | --- | --- |
| `HashLifeEngine` | `hashlife` | Memoizes quadtree updates to reuse spatial and temporal repetition. |
| `StreamLifeEngine` | `streamlife` | Separates non-interacting streams into two universes and caches pairs of HashLife nodes. |
| `SIMDEngine` | Library only | Updates a bit-packed dense grid without quadtree memoization. |

The tree engines use concurrent chained hash tables, per-thread chunk allocators, and work-stealing
queues. Idle workers park while one worker continues looking for work. Garbage collection recycles
unused entries; StreamLife can preserve pending work and resume an update after collection.

Both tree engines support unbounded fields and square tori with power-of-two side lengths of at least 16 cells.
`Pattern` stores a cell configuration as a compact quadtree. It supports `.rle`, `.mc`, and `.mc.gz`
files, population and hash calculation, and replacing cells with metacells. Macrocell formats are
suitable for large recursive patterns; the current macrocell writer requires a nonempty pattern.

## Build and use

Build the CLI from the repository root with a Rust toolchain and native build tools installed:

```sh
cargo build --release --bin gol_engines_cli --features cli_deps
```

Example for a machine with 45 physical cores and room for a 64 GiB engine budget:

```sh
mkdir -p output
target/release/gol_engines_cli update \
    res/very_large_patterns/0e0p-metaglider.mc.gz \
    --engine=streamlife --mem-limit-gib=64 --workers=45 \
    --gens-log2=27 --step-log2=27 \
    --output=output/0e0p-g27.mc.gz --population
```

This advances the input by `2^27` generations and writes the final state. Choose the memory budget
and worker count for your machine. `--engine` defaults to `hashlife`, `--workers` to `1`, and
`--topology` to `unbounded`; `torus` connects opposite field edges.

Inspect a pattern or replace a glider's cells with OTCA metapixels:

```sh
target/release/gol_engines_cli stats res/very_large_patterns/pi.mc.gz
mkdir -p output
target/release/gol_engines_cli metafy \
    res/glider.rle res/otca_0.mc.gz res/otca_1.mc.gz \
    --output=output/otca-metaglider.mc.gz --population
```

`metafy --k=N` repeats the replacement `N` times. Use `--help` on any subcommand for its options.
Optional per-thread runtime statistics can be enabled with `--features cli_deps,statistics` at build time.

## Choosing parameters

- **Generations and step.** `--gens-log2=G` adds `2^G` generations to the input state.
  `--step-log2=S` advances by `2^S` at a time; it defaults to `G` and must not exceed it.
  For example, G36/S29 requests 128 successful updates, unless memory pressure forces smaller steps.
- **Memory.** `--mem-limit-gib` is a positive integer table-sizing budget, not a hard RSS limit.
  Leave room for the OS, task metadata, allocation overhead, and pattern loading and serialization.
  Too little memory can cause repeated collection and expensive retries.
- **Step size.** Larger steps can exploit more repetition but need more intermediate cached state.
  Compare complete sequences of updates. Changing the step triggers GC; a fixed step permits cache reuse.
- **Workers.** More cores help when the pattern exposes independent work. Expensive patterns such as
  the Pi calculator can still have limited parallelism. Measure elapsed time and CPU consumption;
  distinguish physical cores from SMT threads.

StreamLife attempts work-preserving GC internally. If an engine returns a recoverable failure,
its previous pattern is retained. The CLI retries at the same step when the previous attempt
succeeded; otherwise it decreases `S` by two, reducing the number of generations per update fourfold.
`S0` and `S1` are terminal steps: if the update and any permitted retry fail, the CLI returns an error
without reducing the step further.

## Performance

StreamLife measurements with engine sources matching
[`b0ab6e7`](https://github.com/das67333/gol_engines/commit/b0ab6e76a703af93eb6df6a665203f4bc1840006),
on a Google Cloud C3D VM with AMD EPYC 9B14: 45 workers pinned to 45 physical cores, one SMT thread
per core. Rust 1.98 release build, statistics disabled, frame pointers enabled. Each input starts at
generation zero with cold caches; times are means of two fresh-process runs.

| Pattern | Generations | Step | Budget, GiB | Update time, s | Peak RSS, GiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0E0P metaglider | `2^27` | `2^27` | 64 | 32.2 | 30.0 |
| 0E0P metaglider | `2^29` | `2^26` | 128 | 626.7 | 109.5 |
| Pi calculator | `2^28` | `2^28` | 8 | 2.24 | 1.19 |

Update time sums engine calls, including internal GC, and excludes loading, validation, and file I/O.
Peak RSS is the maximum process peak across the two runs. All runs reached their target and matched
expected state hashes and populations. These are fixed-machine measurements; scaling depends on
the pattern, step, and available memory.

The included [0E0P metaglider](res/very_large_patterns/0e0p-metaglider.mc.gz), a glider made of 0E0P
metacells, has also been simulated through `2^36` ordinary Life generations in a checkpointed
calculation. Its final continuation used 45 workers, a 160 GiB engine budget, and steps of `2^29`.
The states at all 128 step boundaries were checked against separate runs of the same engine.
