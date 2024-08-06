# ML-KEM

![verified]

This crate implements all three ML-KEM ([FIPS 203](https://csrc.nist.gov/pubs/fips/203/ipd) (Initial Public Draft)) variants 512, 768, and 1024. It is
formally verified using [hax](https://cryspen.com/hax) and
 [F*](https://fstar-lang.org).

Functions in this crate use CPU feature detection to pick the most efficient version
on each platform. To use a specific version with your own feature detection
use e.g. one of the following

- `mlkem768::avx2::generate_key_pair`,
- `mlkem768::neon::generate_key_pair`,
- `mlkem768::portable::generate_key_pair`,

analogously for encapsulation and decapsulation.

```Rust
 use rand::{rngs::OsRng, RngCore};

 // Ensure you use good randomness.
 // It is not recommended to use OsRng directly!
 // Instead it is highly encouraged to use RNGs like NISTs DRBG to account for
 // bad system entropy.
 fn random_array<const L: usize>() -> [u8; L] {
     let mut rng = OsRng;
     let mut seed = [0; L];
     rng.try_fill_bytes(&mut seed).unwrap();
     seed
 }

 use libcrux_ml_kem::*;

 // This example uses ML-KEM 768. The other variants can be used the same way.

 // Generate a key pair.
 let randomness = random_array();
 let key_pair = mlkem768::generate_key_pair(randomness);

 // Encapsulating a shared secret to a public key.
 let randomness = random_array();
 let (ciphertext, shared_secret) = mlkem768::encapsulate(key_pair.public_key(), randomness);

 // Decapsulating a shared secret with a private key.
 let shared_secret_decapsulated = mlkem768::decapsulate(key_pair.private_key(), &ciphertext);
```

## Features

By default, all ML-KEM parameter sets are enabled. If required, they are
available individually under feature flags `mlkem512`, `mlkem768`,
`mlkem1024`.

In addition to the verified implementations of the ML-KEM variants, the
feature flag `pre-verification` gives access to, as yet, unverified
implementations of ML-KEM that are optimized for SIMD instruction sets.

### Kyber Round 3

The `kyber` flag (in combination with `pre-verification`) also gives access
to an, as yet, unverified implementation of Kyber as submitted in Round 3 of
the NIST PQ competition.

[verified]: https://img.shields.io/badge/verified-brightgreen.svg?style=for-the-badge&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0idXRmLTgiPz48IS0tIFVwbG9hZGVkIHRvOiBTVkcgUmVwbywgd3d3LnN2Z3JlcG8uY29tLCBHZW5lcmF0b3I6IFNWRyBSZXBvIE1peGVyIFRvb2xzIC0tPg0KPHN2ZyB3aWR0aD0iODAwcHgiIGhlaWdodD0iODAwcHgiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj4NCjxwYXRoIGQ9Ik05IDEyTDExIDE0TDE1IDkuOTk5OTlNMjAgMTJDMjAgMTYuNDYxMSAxNC41NCAxOS42OTM3IDEyLjY0MTQgMjAuNjgzQzEyLjQzNjEgMjAuNzkgMTIuMzMzNCAyMC44NDM1IDEyLjE5MSAyMC44NzEyQzEyLjA4IDIwLjg5MjggMTEuOTIgMjAuODkyOCAxMS44MDkgMjAuODcxMkMxMS42NjY2IDIwLjg0MzUgMTEuNTYzOSAyMC43OSAxMS4zNTg2IDIwLjY4M0M5LjQ1OTk2IDE5LjY5MzcgNCAxNi40NjExIDQgMTJWOC4yMTc1OUM0IDcuNDE4MDggNCA3LjAxODMzIDQuMTMwNzYgNi42NzQ3QzQuMjQ2MjcgNi4zNzExMyA0LjQzMzk4IDYuMTAwMjcgNC42Nzc2NiA1Ljg4NTUyQzQuOTUzNSA1LjY0MjQzIDUuMzI3OCA1LjUwMjA3IDYuMDc2NCA1LjIyMTM0TDExLjQzODIgMy4yMTA2N0MxMS42NDYxIDMuMTMyNzEgMTEuNzUgMy4wOTM3MyAxMS44NTcgMy4wNzgyN0MxMS45NTE4IDMuMDY0NTcgMTIuMDQ4MiAzLjA2NDU3IDEyLjE0MyAzLjA3ODI3QzEyLjI1IDMuMDkzNzMgMTIuMzUzOSAzLjEzMjcxIDEyLjU2MTggMy4yMTA2N0wxNy45MjM2IDUuMjIxMzRDMTguNjcyMiA1LjUwMjA3IDE5LjA0NjUgNS42NDI0MyAxOS4zMjIzIDUuODg1NTJDMTkuNTY2IDYuMTAwMjcgMTkuNzUzNyA2LjM3MTEzIDE5Ljg2OTIgNi42NzQ3QzIwIDcuMDE4MzMgMjAgNy40MTgwOCAyMCA4LjIxNzU5VjEyWiIgc3Ryb2tlPSIjMDAwMDAwIiBzdHJva2Utd2lkdGg9IjIiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIgc3Ryb2tlLWxpbmVqb2luPSJyb3VuZCIvPg0KPC9zdmc+