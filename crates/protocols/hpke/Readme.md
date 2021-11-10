# HPKE

![Maturity Level][maturity-badge]
[![Build & Test][github-actions-badge]][github-actions-link]
[![ARM Build][drone-badge]][drone-link]
[![crates.io][crate-badge]][crate-link]
[![Docs][docs-badge]][docs-link]
![Rust Version][rustc-image]

An implementation of [HPKE] with flexible crypto backends.

From the RFC:

> This scheme provides a variant of public-key encryption of arbitrary-sized plaintexts for a recipient public key. It also includes three authenticated variants, including one which authenticates possession of a pre-shared key, and two optional ones which authenticate possession of a KEM private key.

This version is compatible with draft-12, which is expected to be equivalent to the RFC.

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

# Crypto Backends

This crate does not implement the cryptographic primitives used itself.
Instead it expects an implementation of the [HpkeCrypto] trait.

[maturity-badge]: https://img.shields.io/badge/maturity-beta-orange.svg?style=for-the-badge
[github-actions-badge]: https://img.shields.io/github/workflow/status/franziskuskiefer/hpke-rs/Build%20&%20Test?label=build%20%26%20tests&logo=github&style=for-the-badge
[github-actions-link]: https://github.com/franziskuskiefer/hpke-rs/actions/workflows/rust.yml?query=branch%3Amain
[drone-badge]: https://img.shields.io/drone/build/franziskuskiefer/hpke-rs?label=ARM%20BUILD&style=for-the-badge
[drone-link]: https://cloud.drone.io/franziskuskiefer/hpke-rs
[crate-badge]: https://img.shields.io/crates/v/hpke-rs.svg?style=for-the-badge
[crate-link]: https://crates.io/crates/hpke-rs
[docs-badge]: https://img.shields.io/badge/docs-rs-blue.svg?style=for-the-badge
[docs-link]: https://docs.rs/hpke-rs
[evercrypt]: https://github.com/franziskuskiefer/evercrypt-rust
[hpke]: https://cfrg.github.io/draft-irtf-cfrg-hpke/draft-irtf-cfrg-hpke.html
[hpkecrypto]: https://docs.rs/hpke-rs-crypto
[rustc-image]: https://img.shields.io/badge/rustc-1.56+-blue.svg?style=for-the-badge
