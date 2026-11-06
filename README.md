# GoL Engines: parallel HashLife and StreamLife

Tools for Conway's Game of Life, originally part of [conway](https://github.com/das67333/conway/).

[![Crates.io][crates-badge]][crates-url]
[![License: GPL v3][gpl3-badge]][gpl3-url]
[![Build Status][actions-badge]][actions-url]

[crates-badge]: https://img.shields.io/crates/v/gol_engines.svg
[crates-url]: https://crates.io/crates/gol_engines
[gpl3-badge]: https://img.shields.io/badge/license-GPLv3-blue.svg
[gpl3-url]: https://www.gnu.org/licenses/gpl-3.0
[actions-badge]: https://github.com/das67333/gol_engines/actions/workflows/rust.yml/badge.svg
[actions-url]: https://github.com/das67333/gol_engines/actions/workflows/rust.yml

## Contents

- [Overview](#overview)
- [Building](#building)
- [CLI](#cli)
- [Choosing simulation parameters](#choosing-simulation-parameters)
- [Performance measurements](#performance-measurements)

## Overview

The library implements the B3/S23 rule with three engines:

| Engine | CLI value | Approach |
| --- | --- | --- |
| `HashLifeEngine` | `hashlife` | Memoized quadtree updates with parallel task execution. |
| `StreamLifeEngine` | `streamlife` | HashLife-based updates that separate non-interacting streams into two universes. |
| `SIMDEngine` | Library only | Bit-packed dense-grid updates without quadtree memoization. |

HashLife and StreamLife use concurrent chained hash tables backed by per-thread chunk allocators.
The bucket arrays and entry capacities are fixed when an engine is created; entry storage is allocated
in chunks as needed, and garbage collection recycles unused slots. Both engines use worker threads
with work-stealing queues and idle-worker parking.

StreamLife also caches pairs of quadtree nodes. On cache pressure it can collect unused entries while
preserving pending work and resume the current update. If an update still cannot finish, the engine
restores the previous pattern and returns an error to the caller.

The tree engines support two field topologies:

- `unbounded`: the field grows as needed.
- `torus`: opposite edges of a square of side length `2^n` are connected.

`Pattern` stores a cell configuration as a compact quadtree, independently of an engine's runtime
caches. It supports reading and writing `.rle`, `.mc`, and `.mc.gz` files, computing population and
hashes, and replacing cells with metacells. Prefer macrocell formats for large recursive patterns;
the current macrocell writer cannot encode an entirely empty pattern.

## Building

With a current Rust toolchain and a native build toolchain installed, run from the repository root:

```sh
cargo build --release --bin gol_engines_cli --features cli_deps
```

The executable is `target/release/gol_engines_cli`. These instructions describe the source in this
checkout; a published crate or an executable built from an older revision can differ.

Optional per-thread runtime statistics are enabled at build time:

```sh
cargo build --release --bin gol_engines_cli --features cli_deps,statistics
```

Statistics are disabled by default. Use the same feature set when comparing performance.

## CLI

The CLI provides `update`, `metafy`, and `stats`. Get the current argument reference directly from
its executable:

```sh
target/release/gol_engines_cli --help
target/release/gol_engines_cli update --help
target/release/gol_engines_cli metafy --help
target/release/gol_engines_cli stats --help
```

### Update

Advance the supplied pattern by a power-of-two number of generations:

```sh
mkdir -p output
target/release/gol_engines_cli update \
    res/very_large_patterns/0e0p-metaglider.mc.gz \
    --engine=hashlife \
    --mem-limit-gib=12 \
    --workers=16 \
    --gens-log2=12 \
    --output=output/0e0p-g4096.mc.gz \
    --population
```

This example adds 4096 generations to the input state. Resource settings are examples, not universal
defaults; choose them for the available machine and pattern.

| Option | Meaning |
| --- | --- |
| `--output`, `-o` | Required output path. The resulting pattern is written after the whole update finishes; the file extension selects the format. |
| `--engine`, `-e` | `hashlife` (default) or `streamlife`. |
| `--mem-limit-gib`, `-m` | Required positive integer hash-table memory budget in GiB; not a hard limit on process RSS. |
| `--workers`, `-w` | Positive number of worker threads; defaults to `1`. |
| `--gens-log2`, `-g` | Required exponent: add `2^G` generations to the input state. |
| `--step-log2`, `-s` | Initial per-update exponent `S`: advance by `2^S` generations at a time. Defaults to `G` and must not exceed it. |
| `--topology`, `-t` | `unbounded` (default) or `torus`. |
| `--population`, `-p` | Print the final population. |

Use `--workers=1` to run either tree engine with one worker. The input field must be at least
`8 x 8`; the current update command does not expand smaller inputs before loading them into the engine.

For StreamLife, select `--engine=streamlife`. A separate step size can be supplied with
`--step-log2`; see [Choosing simulation parameters](#choosing-simulation-parameters).

### Metafy

Replace each dead or live cell with the corresponding metacell:

```sh
mkdir -p output
target/release/gol_engines_cli metafy \
    res/glider.rle res/otca_0.mc.gz res/otca_1.mc.gz \
    --output=output/metaglider.mc.gz \
    --population
```

`--k` controls how many times to repeat the replacement: the default is `1`, and `--k=0` leaves
the cell configuration unchanged. Repeated replacement can produce very large patterns.

### Stats

Print the pattern hash, population, and distribution of quadtree node sizes:

```sh
target/release/gol_engines_cli stats res/very_large_patterns/pi.mc.gz
```

## Choosing simulation parameters

### Generation count and step size

`G` and `S` are exponents, not generation counts. For example, `--gens-log2=36 --step-log2=29`
requests `2^36` additional generations in 128 updates of `2^29` generations, provided the CLI does
not reduce the step after a failure. The generation count is relative to the input pattern.

A larger step can exploit more temporal repetition, but can also require more intermediate nodes
and cached results. A smaller step reduces the work attempted in one update, at the cost of more
updates. Its effect on total runtime depends on the pattern and memory budget; the largest possible
step is not always the fastest.

Changing the step between updates triggers garbage collection in both tree engines. Repeating a
fixed step lets later updates reuse caches accumulated by earlier ones. Compare candidate step
sizes over a representative sequence, including cache pressure, rather than just the first update.

When an engine reports a recoverable update failure, the CLI retries at the same step if the
previous attempt succeeded; otherwise it reduces `S` by 2, dividing the step by four. StreamLife may
perform its own work-preserving GC before returning such a failure. The current CLI's fallback
panics if it needs to reduce `S` below zero from `0` or `1`.

### Memory

Leave RAM available for the operating system, task metadata, allocator overhead, pattern loading,
and serialization. `--mem-limit-gib` controls table sizing, not the total resident memory of the
process. Bucket counts are powers of two; entry storage and the split between HashLife nodes and
StreamLife's pair cache also affect usable capacity.

Too small a budget can cause repeated collection, failed updates, and step reductions. Performance
comparisons should use the same memory budget and record whether either run encountered this
pressure.

### Workers

Useful parallelism depends on the available independent work, not just the population or bounding-box
size. Some expensive patterns, including the Pi calculator, offer limited parallelism.
More workers can then spend time finding work without reducing the elapsed time.

Measure several worker counts on the target pattern and machine. Distinguish physical cores from
SMT threads when reporting results, and include process CPU time as well as elapsed time.

## Performance measurements

For a reproducible comparison, record the source revision, build features, input state, generation
count, step size, topology, memory budget, worker count, and hardware. Report engine update time
separately from whole-command time: the CLI's update timer excludes initialization, loading, final
population counting, and output serialization. Check output states as well as timings. A loaded
pattern starts with cold runtime caches, so a resumed segment is not equivalent to the same segment
within an uninterrupted run.

The tables below are retained as **historical results for version 0.2.0**, not measurements of the
current engine or its scaling. They used a Yandex Cloud VM with 32 logical cores and 96 GiB RAM;
each engine had at least 64 GiB available. Golly was version 4.3, lifelib was built with clang-19
and `-O3 -march=native`, and gol_engines used Rust 1.87 in release mode. The old HashLife Async
engine used 24 workers; the old StreamLife Async engine used 6.

Updating 0E0P by `2^14` generations with the historical HashLife implementations (seconds):

| Implementation | Initialization | Update |
| --- | ---: | ---: |
| lifelib | - | 912.1 |
| Golly | - | 848.5 |
| HashLifeEngineSmall | - | 642.1 |
| HashLifeEngineSync | 23.8 | 431.5 |
| HashLifeEngineAsync | 25.4 | 41.7 |

Updating 0E0P by `2^27` generations with the historical StreamLife implementations (seconds):

| Implementation | Initialization | Update |
| --- | ---: | ---: |
| lifelib | - | 991.1 |
| StreamLifeEngineSmall | - | 742.5 |
| StreamLifeEngineSync | 26.3 | 533.4 |
| StreamLifeEngineAsync | 26.9 | 186.9 |
