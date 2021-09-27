![Maturity Level][maturity-badge]
[![Build & Test][github-actions-badge]][github-actions-link]
[![ARM Build][drone-badge]][drone-link]
[![crates.io][crate-badge]][crate-link]
[![Docs][docs-main-badge]][docs-main-link]

An implementation of [HPKE] using [Evercrypt].

This version is compatible with draft-12.

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

## Other Crypto Backend

Because [Evercrypt] does not support all platforms and algorithms at this point it is possible to use an alternative cryptography backend.

In order to use the alternative rust crypto backend,
([hkdf], [sha2], [p256], [p384], [x25519-dalek-ng], [chacha20poly1305], [aes-gcm])
the default features have to disabled and the `rust-crypto` feature has to be enabled.
```ignore
cargo build --no-default-features --features="rust-crypto"
```

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

[hkdf]: https://docs.rs/hkdf/
[sha2]: https://docs.rs/sha2
[p256]: https://docs.rs/p256
[p384]: https://docs.rs/p384
[x25519-dalek-ng]: https://docs.rs/x25519-dalek-ng
[chacha20poly1305]: https://docs.rs/chacha20poly1305
[aes-gcm]: https://docs.rs/aes-gcm
