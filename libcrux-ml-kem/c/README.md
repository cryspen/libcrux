# ML-KEM 768 C

This folder contains a header only C extract of the libcrux ml-kem crate for ML-KEM 768.

To re-generate the C coder, run the following in the ml-kem crate.

```bash
./c.sh --config cg.yaml --mlkem768 --no-glue --no-unrolling --no-karamel_include \
    --out c
```

Note that building this code with C++ requires C++ 20 for support of designated initializers.

## Build

Make sure to use `CC=clang CXX=clang++` when benchmarking on Linux to get full performance.

```bash
cmake -B build -G "Ninja Multi-Config"
cmake --build build
```

To enable neon builds, set `LIBCRUX_NEON=1`.

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
