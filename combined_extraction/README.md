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

Set `LIBCRUX_KYBER=1` before cmake to also build the optional Kyber 768
compatibility test (not part of the combined extraction itself).

Enable ASan/UBSan (GCC/Clang) or ASan (MSVC) with `-DENABLE_SANITIZERS=ON`,
off by default:

```bash
cmake -B build -DENABLE_SANITIZERS=ON
cmake --build build
```
