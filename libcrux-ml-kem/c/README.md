# ML-KEM

This folder contains the extracted ML-KEM C code.

## Generating C code

The C code is generated from Rust using [Charon], [Eurydice] and [Karamel].
The [c.sh](../c.sh) bash script drives the extraction, using the [c.yaml](../c.yaml)
configuration file.
While running the commands separately is possible, it is not recommended because
the script sets all necessary configuration flags.

## Build

```bash
cmake -B build -G "Ninja Multi-Config"
cmake --build build
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
