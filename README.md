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

The tree engines share memoization tables with concurrent chaining, allocate entries in per-thread
chunks, and distribute work through work-stealing queues. StreamLife parks idle workers and can
preserve pending work across garbage collection.

Both tree engines support unbounded fields and square tori with power-of-two side lengths.
`Pattern` stores a cell configuration as a compact quadtree. It supports `.rle`, `.mc`, and `.mc.gz`
files, population and hash calculation, and replacing cells with metacells. Macrocell formats are
suitable for large recursive patterns; the current macrocell writer requires a nonempty pattern.

[lifelib](https://gitlab.com/apgoucher/lifelib) provides the original StreamLife implementation,
broader cellular-automaton rule support, and Python/C++ APIs. GoL Engines focuses on running a single
large B3/S23 update across many CPU cores, with a Rust API and CLI. The
[upstream StreamLife recursion](https://gitlab.com/apgoucher/lifelib/-/blob/05632e382096925c0b1724fd59d2f0784f0213d6/streamlife.h#L301-311)
evaluates child problems sequentially; GoL Engines schedules independent work across threads sharing
cached results. The benefit depends on the available parallelism in the pattern. The measurements
below report GoL Engines performance.

## Build and use

Build the CLI from the repository root with a Rust toolchain and native build tools installed:

```sh
cargo build --release --bin gol_engines_cli --features cli_deps
```

Advance the included ticker pattern by `2^12` generations:

```sh
target/release/gol_engines_cli update res/golly-ticker.rle \
    --mem-limit-gib=1 --gens-log2=12 --output=ticker-g12.mc
```

Use `--engine=streamlife` for StreamLife and `--workers=N` to select the number of worker threads.
The defaults are HashLife, one worker, and an unbounded field; `--topology=torus` connects opposite
field edges. Choose the memory budget and worker count for the workload and machine.

Inspect a pattern's population, hash, and quadtree statistics:

```sh
target/release/gol_engines_cli stats res/very_large_patterns/pi.mc.gz
```

Replace a glider's dead and live cells with the corresponding OTCA metapixels:

```sh
target/release/gol_engines_cli metafy \
    res/glider.rle res/otca_0.mc.gz res/otca_1.mc.gz \
    --output=otca-metaglider.mc.gz --population
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
- **Workers.** `--workers=N` creates N computing threads; the calling thread waits for them.
  One worker per physical core is a starting point, not a measured optimum. Compare smaller counts
  and, on SMT machines, counts up to the logical CPU limit. Expensive patterns such as the Pi
  calculator can still have limited parallelism; measure elapsed time and CPU consumption.

StreamLife attempts work-preserving GC internally. If recovery fails, the CLI can retry or reduce
`S` by two (four times fewer generations per update). A smaller step may allow an update to fit,
but can also lose useful memoization; compare complete runs when tuning it.

## Performance

StreamLife on Google Cloud C3D (AMD EPYC 9B14), with 45 workers and process affinity restricted to
one SMT thread on each of 45 physical cores. Engine sources match
[`b0ab6e7`](https://github.com/das67333/gol_engines/commit/b0ab6e76a703af93eb6df6a665203f4bc1840006);
Rust 1.98 release build, statistics disabled, frame pointers enabled. G means `2^G` generations
from the input; S means `2^S` generations per update.

| Pattern | Target / step | Budget, GiB | Time | Peak RSS, GiB |
| --- | --- | ---: | ---: | ---: |
| [0E0P metaglider](res/very_large_patterns/0e0p-metaglider.mc.gz) | G27 / S27 | 64 | 32.2 s | 30.0 |
| 0E0P metaglider | G29 / S26 | 128 | 626.7 s | 109.5 |
| [Pi calculator](res/very_large_patterns/pi.mc.gz) | G28 / S28 | 8 | 2.24 s | 1.19 |
| [0E0P complete_default.mc](https://gitlab.com/apgoucher/slmake/-/blob/57f0f47f1dc7832ce0f5cbb1773fea45f1491b3c/metacell/complete_default.mc) | G36 / S29 | 160 | ~7 h 21 min | 158.23 |

The short benchmarks report mean engine-update time over two runs with cold caches; G36 reports
total computation time. Budget controls table sizes and GC frequency; RSS is measured process memory.

The `complete_default.mc` input exactly matches the first frame of the
[historical 0E0P timeline](https://conwaylife.com/forums/viewtopic.php?p=196996#p196996).
Goucher [reported 30 days with StreamLife](https://conwaylife.com/forums/viewtopic.php?p=65620#p65620)
for a full metatick (`2^36` generations) in 2018.
