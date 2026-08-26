# Combined C Extraction

ML-KEM and ML-DSA extracted from the libcrux Rust implementation into C.
Two output formats are provided.

## Output directories

| Directory        | Format       | ML-KEM variants  | ML-DSA variants |
|------------------|--------------|------------------|-----------------|
| `c/`             | split-source | 512 · 768 · 1024 | 44 · 65 · 87    |
| `c-header-only/` | header-only  | 512 · 768 · 1024 | 44 · 65 · 87    |

**Split-source** (`c/`): separate `.c` and `.h` files.  Build the
`combined_static` library from the `.c` files and link against it.

**Header-only** (`c-header-only/`): every function is `static inline` in its
`.h` file — just include the relevant header and compile, no separate library
step required.

Extraction has only been tested on x64.

## Prerequisites

The following environment variables must be set:

```bash
export CHARON_HOME=...    # path to a Charon checkout
export EURYDICE_HOME=...  # path to a Eurydice checkout
export KRML_HOME=...      # path to a KaRaMeL checkout
```

Run all extraction commands from the `combined_extraction/` directory.

## Extraction commands

```bash
# Both outputs (default — Charon runs once, Eurydice runs twice)
./extract.sh

# Split-source (c/) only
./extract.sh --c-only

# Header-only (c-header-only/) only
./extract.sh --header-only

# Skip Charon (reuse existing .llbc files at the repo root)
./extract.sh --no-charon

# Portable only (disables AVX2)
./extract.sh --portable

# Clean output directory before extracting
./extract.sh --clean
```

Flags can be combined, e.g. `./extract.sh --no-charon --portable --c-only`.

## Building and testing

Each output directory ships a `CMakeLists.txt` with GTest-based tests.

```bash
cd c          # or c-header-only
cmake -B build -G "Ninja Multi-Config"
cmake --build build

# Run individual test binaries, e.g.:
./build/Debug/ml_dsa_test65
./build/Debug/ml_kem_test768
```

The `c/` build defines a `combined_static` library; all test binaries link
against it.  The `c-header-only/` build has no library target — tests include
the headers directly.

`c/tests/` and `c-header-only/tests/` are the same directory
(`c-header-only/tests` is a symlink to `c/tests`). `tests/mlkem.cc` and
`tests/mldsa.cc` are single, variant-parameterized source files — each test
binary compiles the same source with `MLKEM_VARIANT`/`MLDSA_VARIANT` defined
via `target_compile_definitions` (e.g. `ml_kem_test768` compiles `mlkem.cc`
with `MLKEM_VARIANT=768`) to select the right headers, sizes, and symbol
names.

Set `LIBCRUX_KYBER=1` before cmake to also build the optional Kyber 768
compatibility test (not part of the combined extraction itself).

Enable ASan/UBSan (GCC/Clang) or ASan (MSVC) with `-DENABLE_SANITIZERS=ON`,
off by default:

```bash
cmake -B build -DENABLE_SANITIZERS=ON
cmake --build build
```

## Benchmarking

`c/` (not `c-header-only/`) ships Google Benchmark-based benchmarks in
`c/benches/`, gated behind the `LIBCRUX_BENCHMARKS` environment variable so
the dependency is only fetched when needed:

```bash
cd c
LIBCRUX_BENCHMARKS=1 cmake -B build -G "Ninja Multi-Config"
LIBCRUX_BENCHMARKS=1 cmake --build build --config Release

./build/Release/ml_kem_bench768
./build/Release/ml_dsa_bench65
```

With a single-config generator (plain Ninja/Makefiles,
`-DCMAKE_BUILD_TYPE=Release` instead of `-G "Ninja Multi-Config"`), the
binaries land directly in `build/` rather than `build/Release/`.

Like the tests, `benches/mlkem.cc` and `benches/mldsa.cc` are single,
variant-parameterized source files (`MLKEM_VARIANT`/`MLDSA_VARIANT`); each of
the six binaries — `ml_kem_bench512/768/1024` and `ml_dsa_bench44/65/87` —
compiles the same source for its variant. Each binary benchmarks key
generation, encapsulation/decapsulation (ML-KEM) or sign/verify (ML-DSA), for
the portable backend and, on x86_64, the AVX2 backend.

Pass standard Google Benchmark flags to filter or tune a run, e.g.:

```bash
./build/Release/ml_kem_bench768 --benchmark_filter=avx2 --benchmark_min_time=2s
```

### Flamegraphs

`c/scripts/flamegraph.sh` builds (if needed) and profiles a benchmark binary
with [`samply`](https://github.com/mstange/samply) (`cargo install samply`),
opening the recording directly in the [Firefox
Profiler](https://profiler.firefox.com):

```bash
cd c
scripts/flamegraph.sh ml_kem_bench768              # profile everything
scripts/flamegraph.sh ml_kem_bench768 key_generation  # filter to one benchmark
```

Set `LIBCRUX_BENCHMARK_MIN_TIME` (default `5s`) to control how long the
benchmark runs, giving the profiler more samples to work with.
