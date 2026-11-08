# GoL Engines

A Rust library and CLI for Conway's Game of Life (B3/S23), with parallel HashLife and StreamLife.

[![Crates.io](https://img.shields.io/crates/v/gol_engines.svg)](https://crates.io/crates/gol_engines)
[![License: GPL v3](https://img.shields.io/badge/license-GPLv3-blue.svg)](LICENSE)

## Engines and capabilities

| Engine | CLI name | How it works |
| --- | --- | --- |
| `HashLifeEngine` | `hashlife` | Memoizes quadtree updates to reuse spatial and temporal repetition. |
| `StreamLifeEngine` | `streamlife` | Separates non-interacting streams into two universes and caches pairs of HashLife nodes. |

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
cached results. The benefit depends on the available parallelism in the pattern. The benchmarks
below compare both engines with lifelib and Golly.

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

The CLI may reduce the step for either engine if an update does not fit in memory.

## Performance

Benchmarks used a Google Cloud Spot (preemptible) `c3d-highcpu-90` VM in `australia-southeast1`:
45 physical AMD EPYC 9B14 cores, 90 vCPUs, and 180 GiB RAM, at about
[US$0.40/hour](https://cloud.google.com/spot-vms/pricing) for CPU and memory.
Core counts below refer to physical cores, using one hardware thread per core.

The tables compare GoL Engines release builds
([StreamLife `91c795c`](https://github.com/das67333/gol_engines/commit/91c795c752e5397e99a0d82ace5a9aee71b3fa12) and
[HashLife `622bf9e`](https://github.com/das67333/gol_engines/commit/622bf9e2e28df26396b2a53d6811f89942d7b680)) with
[lifelib 2.5.9](https://gitlab.com/apgoucher/lifelib/-/tree/05632e382096925c0b1724fd59d2f0784f0213d6)
and [Golly 5.0](https://golly.sourceforge.io/).
Times are seconds for one update by `2^G` generations from the input, excluding file loading.
Golly and lifelib use one core; columns 1–32 show GoL Engines at that many cores.
Each implementation uses the same memory budget for a given pattern.

**HashLife**

| Pattern | G | Budget, GiB | Golly | lifelib | 1 | 2 | 4 | 8 | 16 | 32 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| [0E0P metaglider](res/very_large_patterns/0e0p-metaglider.mc.gz) | 11 | 64 | 81.33 | 156.17 | 80.69 | 39.06 | 18.88 | 9.85 | 5.13 | 2.72 |
| [Pi calculator](res/very_large_patterns/pi.mc.gz) | 31 | 16 | 4.38 | 3.82 | 2.76 | 2.30 | 2.17 | 2.16 | 2.41 | 2.83 |
| [Demonoid](res/very_large_patterns/0hd-demonoid-p438852.mc.gz) | 20 | 16 | 47.47 | 130.91 | 63.61 | 28.95 | 14.41 | 7.72 | 4.33 | 2.75 |
| [Caterloopillar](res/very_large_patterns/caterloopillar-c17.mc.gz) | 36 | 16 | 6.65 | 8.23 | 4.49 | 2.38 | 1.23 | 0.66 | 0.40 | 0.28 |
| [Mersenne 44497](res/very_large_patterns/mersenne-44497.mc.gz) | 28 | 16 | 1.07 | 2.56 | 1.35 | 1.35 | 1.38 | 1.40 | 1.66 | 1.87 |

**StreamLife**

| Pattern | G | Budget, GiB | lifelib | 1 | 2 | 4 | 8 | 16 | 32 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| [0E0P metaglider](res/very_large_patterns/0e0p-metaglider.mc.gz) | 11 | 64 | 32.90 | 17.64 | 9.08 | 4.45 | 2.60 | 1.56 | 0.96 |
| [Pi calculator](res/very_large_patterns/pi.mc.gz) | 31 | 16 | 7.92 | 5.72 | 3.47 | 3.43 | 3.23 | 4.58 | 5.34 |
| [Demonoid](res/very_large_patterns/0hd-demonoid-p438852.mc.gz) | 20 | 16 | 8.48 | 5.96 | 3.05 | 1.64 | 1.05 | 1.46 | 1.52 |
| [Caterloopillar](res/very_large_patterns/caterloopillar-c17.mc.gz) | 36 | 16 | 18.98 | 11.56 | 5.83 | 2.97 | 1.51 | 0.99 | 0.61 |
| [Mersenne 44497](res/very_large_patterns/mersenne-44497.mc.gz) | 28 | 16 | 5.53 | 3.43 | 2.49 | 3.11 | 3.14 | 4.45 | 4.82 |

On the metaglider at G11, HashLife speeds up 29.6× from 1 to 32 cores; StreamLife speeds up 18.3×
and remains faster in absolute time. Pi and Mersenne have limited parallelism and can slow down
with more workers. Golly is fastest on Mersenne in this comparison.

For a complete 0E0P metatick, StreamLife advances
[`complete_default.mc`](https://gitlab.com/apgoucher/slmake/-/blob/57f0f47f1dc7832ce0f5cbb1773fea45f1491b3c/metacell/complete_default.mc)
by `2^36` generations in **7 h 13 min**, with 45 workers, step `2^29`, a 160 GiB budget,
and 157.23 GiB peak RSS. Budget controls table sizes and GC frequency; RSS is measured process memory.
The input exactly matches the first frame of the
[historical 0E0P timeline](https://conwaylife.com/forums/viewtopic.php?p=196996#p196996).
Goucher [reported 30 days with StreamLife](https://conwaylife.com/forums/viewtopic.php?p=65620#p65620)
for a full metatick in 2018.
