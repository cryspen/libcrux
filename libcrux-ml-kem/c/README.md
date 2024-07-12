<!--
SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>

SPDX-License-Identifier: Apache-2.0
-->

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
