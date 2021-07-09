![Maturity Level][maturity-badge]
[![Build & Test][github-actions-badge]][github-actions-link]
[![ARM Build][drone-badge]][drone-link]
[![crates.io][crate-badge]][crate-link]
[![Docs][docs-main-badge]][docs-main-link]

An implementation of [HPKE] using [Evercrypt].

This version is compatible with draft-09.

## Supported HPKE modes

- Base
- PSK
- Auth
- AuthPSK

## Supported cipher suites

### KEM

- DH KEM x25519
- DH KEM P256

### AEAD

- AES GCM 128
- AES GCM 256
- ChaCha20 Poly1305
- Exporter only

### KDF

- HKDF SHA-256
- HKDF SHA-384
- HKDF SHA-512

[maturity-badge]: https://img.shields.io/badge/maturity-beta-orange.svg?style=for-the-badge
[github-actions-badge]: https://img.shields.io/github/workflow/status/franziskuskiefer/hpke-rs/Build%20&%20Test?label=build%20%26%20tests&logo=github&style=for-the-badge
[github-actions-link]: https://github.com/franziskuskiefer/hpke-rs/actions/workflows/rust.yml?query=branch%3Amain
[drone-badge]: https://img.shields.io/drone/build/franziskuskiefer/hpke-rs?label=ARM%20BUILD&style=for-the-badge
[drone-link]: https://cloud.drone.io/franziskuskiefer/hpke-rs
[crate-badge]: https://img.shields.io/crates/v/hpke-rs.svg?style=for-the-badge
[crate-link]: https://crates.io/crates/hpke-rs
[docs-main-badge]: https://img.shields.io/badge/docs-main-blue.svg?style=for-the-badge
[docs-main-link]: https://www.franziskuskiefer.de/hpke-rs/hpke_rs/index.html
[Evercrypt]: https://github.com/franziskuskiefer/evercrypt-rust
[HPKE]: https://cfrg.github.io/draft-irtf-cfrg-hpke/draft-irtf-cfrg-hpke.html
