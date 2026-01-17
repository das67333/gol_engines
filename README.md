# GoL Engines: top-performing Conway's Game of Life update algorithms, including parallel hashlife

Moved from https://github.com/das67333/conway/

[![Crates.io][crates-badge]][crates-url]
[![License: GPL v3][gpl3-badge]][gpl3-url]
[![Build Status][actions-badge]][actions-url]

[crates-badge]: https://img.shields.io/crates/v/gol_engines.svg
[crates-url]: https://crates.io/crates/gol_engines
[gpl3-badge]: https://img.shields.io/badge/license-GPLv3-blue.svg
[gpl3-url]: https://www.gnu.org/licenses/gpl-3.0
[actions-badge]: https://github.com/das67333/gol_engines/actions/workflows/rust.yml/badge.svg
[actions-url]: https://github.com/das67333/gol_engines/actions?branch%3Amain

## Table of Contents
- [Overview](#overview)
- [Architecture](#architecture)
- [Features](#features)
- [Building](#building)
- [Examples](#examples)
  - [Update](#update)
  - [Metafy](#metafy)
  - [Stats](#stats)
- [Help](#help)
  - [Update Command](#update)
  - [Metafy Command](#metafy)
  - [Stats Command](#stats)
- [Benchmark](#benchmark)
- [Tips](#tips)

## Overview

The repository includes several cross-platform update algorithm implementations for Conway's Game of Life (focusing on [HashLife](https://conwaylife.com/wiki/HashLife) and [StreamLife](https://conwaylife.com/wiki/StreamLife)):

- SIMDEngine is a relatively simple engine performing updates in a pattern-oblivious way: it stores the field in packed (1 bit per cell) row-major format and updates a consecutive group of cells in a few dozens of CPU instructions. It currently updates 64 cells at once and can be easily changed to conditionally use AVX-like instructions.
- HashLifeEngineSmall is similar to the one in [lifelib](https://gitlab.com/apgoucher/lifelib) --- it uses a hashtable with a chaining collision handling technique and stores nodes corresponding to squares of different sizes separately. Nodes of different sizes are indexed independently, zero index corresponds to the blank node. Leaf size is $8\times8$, hash function is [Golly](https://golly.sourceforge.io/)-based `let h = nw * 5 + ne * 17 + sw * 257 + se * 65537; h += h >> 11`.
- StreamLifeEngineSmall is based on HashLifeEngineSmall; it caches results of updates in a single standard hashtable (which is open-addressing) with a fast hash function from [ahash](https://crates.io/crates/ahash/).
- HashLifeEngineSync uses a single pre-allocated open-addressing hashtable with linear probing. Unlike HashLifeEngineSmall, the hashtable never grows. If the hashtable reaches load factor 0.75 during the update, the algorithm temporarily "poisons" the hashtable to quickly terminate the update, clears the hashtable and loads the configuration of cells it stored before the update.
- StreamLifeEngineSync also uses a preallocated open-addresssing hashtable that never grows. If it overfills, the algorithm also "poisons" the hashtables and terminates the update.
- HashLifeEngineAsync is the HashLifeEngineSync that was modified to thread-safely execute in parallel. It uses asynchronous runtime [tokio](https://tokio.rs/). New asynchronous tasks (lightweight threads) for recursive calls are spawned only when processing a square not smaller than a given threshold (`MIN_TASK_SPAWN_SIZE_LOG2`) and total number of running asynchronous tasks is smaller than `MAX_TASKS_COUNT`.
- StreamLifeEngineAsync is like StreamLifeEngineSync, but it is based on HashLifeEngineAsync. Recursive calls to the update function can spawn new asynchronous tasks, like in HashLifeEngineAsync.

Two topologies of the field are supported: Unbounded and Torus  (the latter on a $2^n\times2^n$ square grid).

CLI interface provides access to *Sync and *Async variants.

## Architecture

![architecture](https://github.com/user-attachments/assets/c1755385-a828-4ab4-bcef-5dd9f8b77423)

The `Pattern` structure is designed to be a fast and compact checkpoint for the engines. It stores a configuration of cells in quadtree form (like HashLife).

## Features

- Parallel HashLife and StreamLife!
- Crossplatform
- Right now only supports patterns with B3/S23 rule
- Can read and write .rle, .mc and .mc.gz file formats
- Can efficiently metafy patterns (for example, create multi-level OTCA metapixel)
- Automatically handles overfilled hashtables, follows user memory limitations

## Building

If you don't have Rust installed, these commands should be sufficient (on modern Ubuntu):
```
sudo apt install -y build-essential
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"
```

CLI interface can be compiled with
```
cargo build --release --bin gol_engines_cli --features=cli_deps
```

## Examples

#### Update

Update in one step:
```
$ target/release/gol_engines_cli update \
    res/very_large_patterns/0e0p-metaglider.mc.gz \
    --output=res/temp.mc.gz \
    --mem-limit-gib=12 \
    --workers=16 \
    --gens-log2=12 \
    --population
Initialized engine in 5.5 secs
Loaded pattern in 1.9 secs
Updated pattern by 2^12 generations in 13.8 secs
Population: 93_237_300
```

Overfilled hashtable:
```
$ target/release/gol_engines_cli update \
    res/very_large_patterns/0e0p-metaglider.mc.gz \
    --output=res/temp.mc.gz \
    --mem-limit-gib=6 \
    --workers=16 \
    --gens-log2=12 \
    --population
Initialized engine in 2.7 secs
Loaded pattern in 1.3 secs
2025-05-31T17:13:55.452  Overfilled hashtables, reducing step_log2 from 12 to 10
2025-05-31T17:14:00.764  Updated by 1024 out of 4096 generations
2025-05-31T17:14:04.786  Updated by 2048 out of 4096 generations
2025-05-31T17:14:09.006  Updated by 3072 out of 4096 generations
2025-05-31T17:14:12.680  Overfilled hashtables, running GC
Updated pattern by 2^12 generations in 37.5 secs
Population: 93_237_300
```

Providing step-log2 manually:
```
$ target/release/gol_engines_cli update \
    res/very_large_patterns/0e0p-metaglider.mc.gz \
    --output=res/temp.mc.gz \
    --mem-limit-gib=6 \
    --workers=16 \
    --gens-log2=12 \
    --step-log2=10 \
    --population
Initialized engine in 2.9 secs
Loaded pattern in 1.5 secs
2025-05-31T17:16:42.996  Updated by 1024 out of 4096 generations
2025-05-31T17:16:47.033  Updated by 2048 out of 4096 generations
2025-05-31T17:16:51.217  Updated by 3072 out of 4096 generations
2025-05-31T17:16:54.960  Overfilled hashtables, running GC
Updated pattern by 2^12 generations in 23.6 secs
Population: 93_237_300
```

And with streamlife:
```
$ target/release/gol_engines_cli update \
    res/very_large_patterns/0e0p-metaglider.mc.gz \
    --output=res/temp.mc.gz \
    --mem-limit-gib=13 \
    --workers=6 \
    --gens-log2=18 \
    --engine=streamlife \
    --population
Initialized engine in 6.3 secs
Loaded pattern in 2.3 secs
Updated pattern by 2^18 generations in 67.8 secs
Population: 93_235_655
```

#### Metafy

Let's metafy glider:
```
$ target/release/gol_engines_cli metafy \
    res/glider.rle res/otca_0.mc.gz res/otca_1.mc.gz \
    --output=res/temp.mc.gz \
    --population
Loaded patterns in 0.0 secs
Metafied pattern in 0.0 secs
Population: 593_927
```

With bigger k:
```
$ target/release/gol_engines_cli metafy \
    res/glider.rle res/otca_0.mc.gz res/otca_1.mc.gz \
    --k=10 \
    --output=res/temp.mc.gz \
    --population
Loaded patterns in 0.0 secs
Metafied pattern in 0.0 secs
Population: 155_233_185_229_932_687_224_687_411_801_884_328_181_836_255_094_962_897_687_012_037_389
```

k=0 doesn't modify the pattern:
```
$ target/release/gol_engines_cli metafy \
    res/glider.rle res/otca_0.mc.gz res/otca_1.mc.gz \
    --k=0 \
    --output=res/temp.mc.gz \
    --population
Loaded patterns in 0.0 secs
Metafied pattern in 0.0 secs
Population: 5
```

#### Stats

For 0e0p-metaglider:
```
$ target/release/gol_engines_cli stats \
    res/very_large_patterns/0e0p-metaglider.mc.gz
Hash: 0xc322148cce4e1279
Population: 93_235_805
Distribution of node sizes (side lengths of the squares):
total -> 818007
2^6   -> 36%
2^7   -> 46%
2^8   -> 12%
2^9   ->  3%
Computed stats in 1.0 secs
```

Pi calculator is much smaller:
```
$ target/release/gol_engines_cli stats \
    res/very_large_patterns/pi.mc.gz
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
Computed stats in 0.1 secs
```

## Help

```
$ target/release/gol_engines_cli help
Tools for Conway's Game of Life

Usage: gol_engines_cli <COMMAND>

Commands:
  update  Run the simulation using parallel implementations of the update algorithms
  metafy  Replace every basic cell with a corresponding metacell (see https://conwaylife.com/wiki/Unit_cell) and repeat it k times
  stats   Compute pattern's hash, population and nodes distribution
  help    Print this message or the help of the given subcommand(s)

Options:
  -h, --help     Print help
  -V, --version  Print version
```

#### Update
```
$ target/release/gol_engines_cli help update
Run the simulation using high-performance implementations of the update algorithms

Usage: gol_engines_cli update [OPTIONS] --output <OUTPUT> --mem-limit-gib <MEM_LIMIT_GIB> --gens-log2 <GENS_LOG2> <PATTERN>

Arguments:
  <PATTERN>
          Path to the file containing the pattern; supports .rle, .mc and .mc.gz formats

Options:
  -o, --output <OUTPUT>
          Path to the file where the resulting pattern will be saved

  -e, --engine <ENGINE>
          The engine to use for the simulation
          
          [default: hashlife]

          Possible values:
          - hashlife:      Parallel implementation of HashLife
          - hashlife-st:   Single-threaded implementation of HashLife
          - streamlife:    Parallel implementation of StreamLife
          - streamlife-st: Single-threaded implementation of StreamLife

  -m, --mem-limit-gib <MEM_LIMIT_GIB>
          Maximum memory (in GiB) allocated to the hash tables; all other usage is typically negligible

  -w, --workers <WORKERS>
          The number of worker threads to use for the update; ignored for single-threaded engines
          
          [default: 1]

  -g, --gens-log2 <GENS_LOG2>
          The pattern will be updated by 2^gens_log2 generations

  -s, --step-log2 <STEP_LOG2>
          How many generations to update at once, uses `gens_log2` by default

  -t, --topology <TOPOLOGY>
          The topology of the pattern
          
          [default: unbounded]

          Possible values:
          - unbounded: The pattern is unbounded in all directions
          - torus:     Opposite bounds of the field are stitched together

  -p, --population
          Count population of the resulting pattern

  -h, --help
          Print help (see a summary with '-h')
```

#### Metafy
```
$ target/release/gol_engines_cli help metafy
Replace every basic cell with a corresponding metacell (see https://conwaylife.com/wiki/Unit_cell) and repeat it k times

Usage: gol_engines_cli metafy [OPTIONS] --output <OUTPUT> <PATTERN> <META_0> <META_1>

Arguments:
  <PATTERN>  Path to the file containing the pattern; supports .rle, .mc and .mc.gz formats
  <META_0>   Path to the file containing the off state of the metacell
  <META_1>   Path to the file containing the on state of the metacell

Options:
  -k, --k <K>            The number of times to apply the metacell replacement [default: 1]
  -o, --output <OUTPUT>  Path to the file where the resulting pattern will be saved
  -p, --population       Count population of the resulting pattern
  -h, --help             Print help
```

#### Stats
```
$ target/release/gol_engines_cli help stats
Compute pattern's hash, population and nodes distribution

Usage: gol_engines_cli stats <PATTERN>

Arguments:
  <PATTERN>  Path to the file containing the pattern; supports .rle, .mc and .mc.gz formats

Options:
  -h, --help  Print help
```

## Benchmark

These are the performance results of different implementations of GoL algorithms when updating the 0e0p-metaglider. The benchmarks were conducted on a Yandex.Cloud virtual machine with 32 logical cores and 96 GiB of RAM. Each engine was able to allocate at least 64 GiB of memory, which is sufficient to store all emerging nodes. Golly version 4.3 was used. Lifelib was compiled with clang-19 using the `-O3 -march=native` flags. Gol_engines version 0.2.0 was compiled with cargo (Rust 1.87) in release mode. HashLifeEngineAsync used 24 workers, StreamLifeEngineAsync used 6 workers.

This is updating 0e0p-mataglider by $2^{14}$ generations with HashLife:

| Implementation      | Initialization time | Update time |
| :------------------ | ------------------: | ----------: |
| lifelib             | -                   | 912.1       |
| Golly               | -                   | 848.5       |
| HashLifeEngineSmall | -                   | 642.1       |
| HashLifeEngineSync  | 23.8                | 431.5       |
| HashLifeEngineAsync | 25.4                | 41.7        |

And this is updating 0e0p-mataglider by $2^{27}$ generations with StreamLife:

| Implementation        | Initialization time | Update time |
| :-------------------- | ------------------: | ----------: |
| lifelib               | -                   | 991.1       |
| StreamLifeEngineSmall | -                   | 742.5       |
| StreamLifeEngineSync  | 26.3                | 533.4       |
| StreamLifeEngineAsync | 26.9                | 186.9       |

## Tips

As all the hashtables are power-of-two sized, there are certain memory-limit-gib that double the sizes of them. They are:

- $12 \cdot 2^k$ for hashlife (because hashlife node is 24 bytes in size)
- $13 \cdot 2^k$ for streamlife (because node of internal hashlife is 32 bytes, streamlife node is 20 bytes and these hashtables are initialized with equal capacity)

I reached best performance with about 24 workers for hashlife and 6 workers for streamlife on 96-core virtual machine for 0e0p-metaglider. The best value can depend on the pattern structure and hardware used. You can try other values, but notice that it might be important to provide a whole physical (not logical) core for every worker.

This is updating 0e0p-metaglider with HashLifeEngineAsync by $2^{12}$ generations with different values of `WORKER_THREADS`:

![HashLifeEngineAsync](https://github.com/user-attachments/assets/7f0ee110-56fd-48e1-8acb-bcc103e53dd6)


This is the same for $2^{15}$ generations and StreamLifeEngineAsync:

![StreamLifeEngineAsync](https://github.com/user-attachments/assets/15f900fb-953a-40f5-bae4-b85b30385660)


Small patterns (even the pi calculator) cannot benefit from parallelization as their simulations don't involve enough operations that can be performed independently or such operations are too lightweight.
