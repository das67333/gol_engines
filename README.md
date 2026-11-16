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
suitable for large recursive patterns.

[lifelib](https://gitlab.com/apgoucher/lifelib) provides the original StreamLife implementation,
broader cellular-automaton rule support, and Python/C++ APIs. GoL Engines focuses on running a single
large B3/S23 update across many CPU cores, with a Rust API and CLI. The
[upstream StreamLife recursion](https://gitlab.com/apgoucher/lifelib/-/blob/05632e382096925c0b1724fd59d2f0784f0213d6/streamlife.h#L301-311)
evaluates child problems sequentially; GoL Engines schedules independent work across threads sharing
cached results. The benefit depends on the available parallelism in the pattern. The benchmarks
below compare both engines with lifelib and Golly.

## Build and use

Install the published CLI with `cargo install gol_engines --features cli_deps --bin gol_engines_cli`.
To build from the repository, use Rust 1.89 or newer and native build tools:

```sh
cargo build --release --bin gol_engines_cli --features cli_deps
```

Advance the included ticker pattern by `2^12` generations:

```sh
target/release/gol_engines_cli update res/golly-ticker.rle \
    --mem-limit-gib=1 --gens-log2=12 --output=ticker-g12.mc
```

```text
Initialized and loaded in 0.0 secs; generation 0/4096
Time spent on hashlife executor: 37.756833ms
Nodes count: 234802 / 16777216
2026-11-15T23:02:52.164  Generation 4096/4096; S12; step 0.04s; elapsed 0.0s
Saved /private/tmp/gol_engines/ticker-g12.mc at generation 4096
```

Use `--engine=streamlife` for StreamLife and `--workers=N` to select the number of worker threads.
The defaults are HashLife, one worker, and an unbounded field; `--topology=torus` connects opposite
field edges. Choose the memory budget and worker count for the workload and machine.

Inspect a pattern's population, hash, and quadtree statistics:

```sh
target/release/gol_engines_cli stats res/very_large_patterns/pi.mc.gz
```

```text
Hash: 0xd9c1db4109c7b2ab
Population: 1_189_325
Distribution of node sizes (side lengths of the squares):
total -> 19699
2^3   -> 15%
2^4   -> 34%
2^5   -> 24%
2^6   ->  9%
2^7   ->  5%
2^8   ->  2%
2^9   ->  2%
2^10  ->  2%
2^11  ->  1%
2^12  ->  1%
Computed stats in 0.0 secs
```

Replace a glider's dead and live cells with the corresponding OTCA metapixels:

```sh
target/release/gol_engines_cli metafy \
    res/glider.rle res/otca_0.mc.gz res/otca_1.mc.gz \
    --output=otca-metaglider.mc.gz --population
```

```text
Loaded patterns in 0.0 secs
Metafied pattern in 0.0 secs
Population: 593_927
```

`metafy --k=N` repeats the replacement `N` times. Use `--help` on any subcommand for its options.
Optional per-thread runtime statistics can be enabled with `--features cli_deps,statistics` at build time.

## Long simulations

Add `--checkpoint-dir=run` to `update` to save the initial state and each completed step, retaining
the latest checkpoint.
Resume with `gol_engines_cli resume run`; the target generation and settings are saved automatically.
`resume` accepts `--workers` and `--mem-limit-gib` overrides.

Ctrl+C cancels the unfinished step and rolls back to the last completed state; it does not wait for
that step to finish. Cleanup can take time. A second Ctrl+C exits immediately, leaving the last
saved checkpoint available.

Checkpoints contain the pattern, generation and run settings. They replace the
previous checkpoint only after the new snapshot is written, and validate its checksum on resume.
They do not preserve the in-memory computation caches: resuming starts with cold caches. Keep the
checkpoint directory on persistent storage when using a preemptible VM.

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

Scaling benchmarks used a Google Cloud Spot (preemptible) `c3d-highcpu-90` VM in `australia-southeast1`:
45 physical AMD EPYC 9B14 cores, 90 vCPUs, and 180 GiB RAM, at about
[US$0.40/hour](https://cloud.google.com/spot-vms/pricing) for CPU and memory.
Core counts below refer to physical cores, using one hardware thread per core.

The scaling tables compare GoL Engines 0.3.2 release builds with
[lifelib 2.5.9](https://gitlab.com/apgoucher/lifelib/-/tree/05632e382096925c0b1724fd59d2f0784f0213d6)
and [Golly 5.0](https://golly.sourceforge.io/).
Times are seconds for one update by `2^G` generations from the input, excluding file loading.
Golly and lifelib use one core. Columns 1–32 show GoL Engines at that many physical cores.
Within each row, all implementations used the same memory budget, chosen so each algorithm had
room for all the nodes it created during the update.
Doubling the generation count required GC in GoL Engines except for Caterloopillar and Hippo.69's
0E0P construction. Caterloopillar also fit at G120 with 16 GiB; the construction's time and memory
stayed nearly constant from G29 through G100.

**HashLife**

| Pattern | G | Budget, GiB | Golly | lifelib | 1 | 2 | 4 | 8 | 16 | 32 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| [0E0P metaglider](res/very_large_patterns/0e0p-metaglider.mc.gz) | 14 | 40 | 701.22 | 1398.42 | 708.43 | 332.45 | 175.01 | 86.21 | 44.36 | 22.78 |
| [0E0P construction (Hippo.69)](res/very_large_patterns/0e0pcells6.mc.gz) | 100 | 48 | 772.88 | 707.73 | 437.57 | 222.77 | 123.32 | 82.61 | 77.46 | 78.81 |
| [Pi calculator](res/very_large_patterns/pi.mc.gz) | 37 | 16 | 54.87 | 122.29 | 53.46 | 51.45 | 51.38 | 51.79 | 60.41 | 65.15 |
| [Demonoid](res/very_large_patterns/0hd-demonoid-p438852.mc.gz) | 21 | 16 | 96.40 | 277.99 | 112.23 | 55.49 | 27.57 | 13.97 | 8.26 | 4.79 |
| [Caterloopillar](res/very_large_patterns/caterloopillar-c17.mc.gz) | 100 | 16 | 6.74 | 8.33 | 4.01 | 2.08 | 1.10 | 0.62 | 0.45 | 0.33 |
| [Mersenne 44497](res/very_large_patterns/mersenne-44497.mc.gz) | 34 | 16 | 54.98 | 134.02 | 59.99 | 60.23 | 60.72 | 61.69 | 69.83 | 73.35 |

**StreamLife**

| Pattern | G | Budget, GiB | lifelib | 1 | 2 | 4 | 8 | 16 | 32 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| [0E0P metaglider](res/very_large_patterns/0e0p-metaglider.mc.gz) | 27 | 48 | 1319.78 | 658.43 | 337.02 | 174.00 | 92.25 | 53.70 | 33.16 |
| [0E0P construction (Hippo.69)](res/very_large_patterns/0e0pcells6.mc.gz) | 100 | 56 | 1048.85 | 733.37 | 376.69 | 195.53 | 110.74 | 90.82 | 79.36 |
| [Pi calculator](res/very_large_patterns/pi.mc.gz) | 37 | 16 | 256.28 | 151.51 | 100.30 | 93.17 | 99.39 | 160.56 | 174.14 |
| [Demonoid](res/very_large_patterns/0hd-demonoid-p438852.mc.gz) | 30 | 16 | 350.57 | 201.33 | 101.51 | 57.42 | 36.19 | 51.81 | 54.07 |
| [Caterloopillar](res/very_large_patterns/caterloopillar-c17.mc.gz) | 100 | 16 | 19.19 | 11.40 | 5.82 | 2.98 | 1.60 | 1.09 | 0.83 |
| [Mersenne 44497](res/very_large_patterns/mersenne-44497.mc.gz) | 34 | 16 | 277.30 | 174.86 | 125.02 | 122.62 | 132.63 | 206.65 | 220.86 |

On the original 0E0P metaglider, moving from 1 to 32 cores sped up HashLife 31.1× at G14
and StreamLife 19.9× at G27. For the same G14 update on 32 cores with 40 GiB, StreamLife took 1.16 s
and HashLife took 22.78 s. On Hippo.69's construction at G100, HashLife was faster on 1–16 cores
and similar to StreamLife on 32 cores. GoL Engines HashLife also completed G100 on 32 cores without
GC at a 36 GiB budget (34.56 GiB peak RSS); the table uses 48 GiB so Golly fits too.

Full 0E0P metatick benchmarks (`2^36` generations) used StreamLife on a Spot `c3d-standard-90` VM
with 360 GiB RAM in the same region, at about
[US$0.53/hour](https://cloud.google.com/spot-vms/pricing) for CPU and memory.
Runs used 45 workers and steps of `2^29` generations:

| Pattern | Budget, GiB | Total time | Peak RSS, GiB |
| --- | ---: | ---: | ---: |
| [`complete_default.mc`](https://gitlab.com/apgoucher/slmake/-/blob/57f0f47f1dc7832ce0f5cbb1773fea45f1491b3c/metacell/complete_default.mc) | 160 | 5 h 44 min 37 s | 173.87 |
| [`complete_default.mc`](https://gitlab.com/apgoucher/slmake/-/blob/57f0f47f1dc7832ce0f5cbb1773fea45f1491b3c/metacell/complete_default.mc) | 288 | 3 h 25 min 24 s | 303.65 |
| [0E0P metaglider](res/very_large_patterns/0e0p-metaglider.mc.gz) | 288 | 3 h 59 min 35 s | 306.84 |

With the same build, increasing the budget from 160 to 288 GiB reduced `complete_default.mc`'s total time by 40.4%.
Budget controls table sizes and GC frequency; RSS is measured process memory.
`mimalloc` can round allocations up, and transparent huge pages (THP) can make the padding resident.
The `complete_default.mc` input exactly matches the first frame of the
[historical 0E0P timeline](https://conwaylife.com/forums/viewtopic.php?p=196996#p196996).
Goucher [reported 30 days with StreamLife](https://conwaylife.com/forums/viewtopic.php?p=65620#p65620)
for a full metatick in 2018.
