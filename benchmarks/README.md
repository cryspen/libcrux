# Libcrux Benchmarks

This crate is used to benchmark libcrux and compare it to 3rd party implementations.

## lib25519
Comparing with lib25519 only works on Linux.
To enable it first build the sys crate 

```bash
cd ../sys/lib25519
./build-native.sh

RUSTFLAGS="--cfg crypto_lib25519" cargo criterion --bench x25519
```
