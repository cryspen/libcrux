# Benchmarks

The benchmarks are run with

```sh
cargo bench
```

or (this requires installing the binary `cargo install criterion`)

```sh
cargo criterion
```

The results can be read from the command line or from the report in `target/criterion/reports/index.html`.

## Filter

Running all benchmarks can take a while.
They can be filtered by benchmark file or individual benchmark.

To execute all SHA 2 benchmarks with all comparison, run

```sh
cargo criterion --bench sha2
```
