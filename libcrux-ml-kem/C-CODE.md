# Extraction into C code

The folders `./c` and `./cg` contain C code extracted from `libcrux-ml-kem`.

The C code is generated from Rust using [Charon], [Eurydice] and
[KaRaMeL]. Charon translates the Rust crate to Low-Level Borrow
Calculus (LLBC). From LLBC, Eurydice translates to KaRaMeL's internal
AST, which is then lowered to C.

## Prerequisites
We assume you have [`rustup`](https://rustup.rs/) and [`opam`](https://ocaml.org/docs/installing-ocaml#1-install-opam) installed.

First, install the tools' dependencies via `opam`:
```bash
opam switch creat 4.13.1+options
opam install --yes ocamlfind visitors menhir ppx_deriving_yojson core_unix sedlex wasm fix process pprint zarith yaml easy_logging terminal
```

Now you're ready to install the tools.
### Set tool directories
Set the directories where tool repositories should be cloned and tools should be built in. Setting these environment variables is important for the extraction script `c.sh`.
```bash
export CHARON_HOME=$HOME/charon
export KRML_HOME=$HOME/karamel
export EURYDICE_HOME=$HOME/eurydice
```

### Charon
```bash
git clone https://github.com/AeneasVerif/charon.git $CHARON_HOME
cd $CHARON_HOME
make
```

### KaRaMeL
```bash
git clone https://github.com/FStarLang/karamel.git $KRML_HOME
cd $KRML_HOME
make
```

### Eurydice
```bash
git clone https://github.com/AeneasVerif/eurydice.git $EURYDICE_HOME
cd $EURYDICE_HOME
make
```

## Generating C code

The [c.sh](../c.sh) bash script drives the extraction, using the
[c.yaml](../c.yaml) configuration file, which configures the Eurydice
translation.

To generate a header-only version, use [boring.sh](../boring.sh)
instead, which internally runs [c.sh](../c.sh) with a header-only
configuration found in [cg.yaml](../cg.yaml).

While running the commands separately is possible, it is not
recommended because the script sets all necessary configuration flags.

## Build

Make sure to use `CC=clang CXX=clang++` when benchmarking on Linux to get full performance.

```bash
cd ./c               # or ./cg, if you want to build header-only
cmake -B build
cmake --build build
```

To enable neon builds, set `LIBCRUX_NEON=1`.

### Symcrypt benchmarks

First get and build symcrypt and set `SYMCRYPT_PATH` for the build.
Ensure you have `elftools` installed (`pip install pyelftools`).

```bash
git clone https://github.com/microsoft/symcrypt
cd symcrypt
git checkout b070a5d236a4d40aa90524cb5b492463c5452b40
scripts/build.py cmake build --config Release
```

```bash
SYMCRYPT_PATH=<your-path> CC=clang CXX=clang++ cmake -B build -G Ninja Multi-Config"
cmake --build build --config Release
./build/Release/ml_kem_bench
```

#### MSVC

To build with MSVC, manual fixes are required.

1. Build symcrypt

```bash
cmake -S . -B bin -DCMAKE_BUILD_TYPE=Release
cmake --build bin --config Release
```

2. Patch symcrypt

```bash
git apply fix-symcrypt-includes.patch
```

3. Build benchmarks as described above.
4. Copy the dll into the binary directory.

```bash
cp ..\..\..\symcrypt\bin\exe\symcrypt.dll .\build\Release\
```

5. Run benchmarks

### Test
If you're on windows, run
```bash
cd ./c               # or ./cg, if you want to test header-only
./build/Debug/ml_kem_test
```
otherwise
```bash
cd ./c               # or ./cg, if you want to test header-only
./c/build/ml_kem_test
```

### Benchmark
```
cd ./c               # or ./cg, if you want to benchmark header-only
rm -rf build
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --config Release
```
[Charon]: https://github.com/AeneasVerif/charon/
[Eurydice]: https://github.com/AeneasVerif/eurydice
[KaRaMeL]: https://github.com/FStarLang/karamel
