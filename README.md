# GoL Engines: top-performance Conway's Game of Life update algorithms, including parallel hashlife

Moved from https://github.com/das67333/conway/

## Overview

The repository includes several cross-platform update algorithm implementations for Conway's Game of Life (focusing on [HashLife](https://conwaylife.com/wiki/HashLife) and [StreamLife](https://conwaylife.com/wiki/StreamLife)):

- SIMDEngine is a relatively simple engine performing updates in a pattern-oblivious way: it stores the field in packed (1 bit per cell) row-major format and updates a consecutive group of cells in a few dozens of CPU instructions. It currently updates 64 cells at once and can be easily changed to conditionally use AVX-like instructions.
- HashLifeEngineSmall is similar to the one in [lifelib](https://gitlab.com/apgoucher/lifelib) --- it uses a hashtable with a chaining collision handling technique and stores nodes corresponding to squares of different sizes separately. Nodes of different sizes are indexed independently, zero index corresponds to the blank node. Leaf size is $8\times8$, hash function is [Golly](https://golly.sourceforge.io/)-based `let h = nw * 5 + ne * 17 + sw * 257 + se * 65537; h += h >> 11`.
- StreamLifeEngineSmall is based on HashLifeEngineSmall; it caches results of updates in a single standard hashtable (which is open-addressing) with a fast hash function from [ahash](https://crates.io/crates/ahash/).
- HashLifeEngineSync uses a single pre-allocated open-addressing hashtable with linear probing. Unlike HashLifeEngineSmall, the hashtable never grows. If the hashtable reaches load factor 0.75 during the update, the algorithm temporarily "poisons" the hashtable to quickly terminate the update process, clears the hashtable and loads the configuration of cells it stored before the update.
- StreamLifeEngineSync is like StreamLifeEngineSmall, but it is based on HashLifeEngineSync.
- HashLifeEngineAsync is the HashLifeEngineSync that was modified to thread-safely execute in parallel. It uses asynchronous runtime [tokio](https://tokio.rs/). New asynchronous tasks (lightweight threads) for recursive calls are spawned only when processing a square not smaller than a given threshold (`MIN_TASK_SPAWN_SIZE_LOG2`) and total number of running asynchronous tasks is smaller than `MAX_TASKS_COUNT`.
-

Two topologies of the field are supported: Unbounded and Torus  (the latter on a $2^n\times2^n$ square grid).

## Architecture

TODO add picture

The structure `Pattern` is designed to be a fast and compact checkpoint for the engines. It stores a configuration in quadtree form, and provides methods for computing hashes for quick patterns comparison (with a tiny chance of collision) and counting precise population using arbitrary big integers.

## Features

- Parallel HashLife and StreamLife!
- Right now only supports patterns with B3/S23 rule
- Can read and write .rle, .mc and .mc.gz file formats
- Can efficiently metafy patterns (build multi-level OTCA metapixel)

## Usage

TODO

## Examples

### Update

```

```

### Help
```
$ target/release/gol_engines_cli help
Tools for Conway's Game of Life

Usage: gol_engines_cli <COMMAND>

Commands:
  update  Run the simulation
  metafy  Replace every basic cell with a corresponding metacell (see https://conwaylife.com/wiki/Unit_cell) and repeat it k times
  help    Print this message or the help of the given subcommand(s)

Options:
  -h, --help     Print help
  -V, --version  Print version
```

```
$ target/release/gol_engines_cli help update
Run the simulation using parallel implementations of the update algorithms

Usage: gol_engines_cli update [OPTIONS] --output <OUTPUT> --engine <ENGINE> --mem-limit-gib <MEM_LIMIT_GIB> --workers <WORKERS> --gens-log2 <GENS_LOG2> <PATTERN>

Arguments:
  <PATTERN>
          Path to the file containing the pattern; supports .rle, .mc and .mc.gz formats

Options:
  -o, --output <OUTPUT>
          Path to the file where the resulting pattern will be saved

  -e, --engine <ENGINE>
          The engine to use for the simulation, default is hashlife

          Possible values:
          - hashlife:  See https://conwaylife.com/wiki/HashLife
          - steamlife: See https://conwaylife.com/wiki/StreamLife

  -m, --mem-limit-gib <MEM_LIMIT_GIB>
          Maximum memory (in GiB) allocated to the hash tables; all other usage is typically negligible

  -w, --workers <WORKERS>
          The number of worker threads to use for the update

  -g, --gens-log2 <GENS_LOG2>
          The pattern will be updated by 2^gens_log2 generations

  -s, --step-log2 <STEP_LOG2>
          How many generations to update at once, uses `gens_log2` by default

  -t, --topology <TOPOLOGY>
          The topology of the pattern, default is unbounded

          Possible values:
          - unbounded: The pattern is unbounded in all directions
          - torus:     Opposite bounds of the field are stitched together

  -h, --help
          Print help (see a summary with '-h')
```

```
$ target/release/gol_engines_cli help metafy
Replace every basic cell with a corresponding metacell (see https://conwaylife.com/wiki/Unit_cell) and repeat it k times

Usage: gol_engines_cli metafy [OPTIONS] --output <OUTPUT> <PATTERN> <META_0> <META_1>

Arguments:
  <PATTERN>  Path to the file containing the pattern; supports .rle, .mc and .mc.gz formats
  <META_0>   Path to the file containing the off state of the metacell
  <META_1>   Path to the file containing the on state of the metacell

Options:
  -k, --k <K>            The number of times to apply the metacell replacement, default is 1 [default: 1]
  -o, --output <OUTPUT>  Path to the file where the resulting pattern will be saved
  -h, --help             Print help
```

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

TODO: tables, scalability
