# Benchmarks
To run HACL* (C) benchmarks, just run `cargo bench` in this crate.
For the HACL-rs version, run `cargo bench --features hacl-rs`.

To get flamegraphs, run
```
cargo bench --bench curve25519 -- --profile-time=5
```
or
```
cargo bench --bench curve25519 --features hacl-rs -- --profile-time=5
```

The flamegraphs can then be found in `../target/criterion/Curve\
25519/{ECDH/Secret\ to\ Public}/profile/flamegraph.svg`.
