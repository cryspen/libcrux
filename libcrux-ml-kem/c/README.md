# ML-KEM

This folder contains the extracted ML-KEM C code.

## Generating C code

The C code is generated from Rust using [Charon], [Eurydice] and [Karamel].
The [c.sh](../c.sh) bash script drives the extraction, using the [c.yaml](../c.yaml)
configuration file.
While running the commands separately is possible, it is not recommended because
the script sets all necessary configuration flags.

## Build

Make sure to use `CC=clang CXX=clang++` when benchmarking on Linux to get full performance.

```bash
cmake -B build -G "Ninja Multi-Config"
cmake --build build
```

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
SYMCRYPT_PATH=<your-path> CC=clang CXX=clang++ cmake -B build -G "Ninja Multi-Config"
cmake --build build --config Release
./build/Release/ml_kem_bench
```

### Test

```bash
./build/Debug/ml_kem_test
```

## Benchmarks

```bash
cmake -B build -G "Ninja Multi-Config"
cmake --build build --config Release
./build/Release/ml_kem_bench
```

[Charon]: https://github.com/AeneasVerif/charon/
[Eurydice]: https://github.com/AeneasVerif/eurydice
[Karamel]: https://github.com/FStarLang/karamel
