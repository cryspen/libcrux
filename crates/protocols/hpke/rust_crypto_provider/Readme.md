# HPKE Crypto provider using native Rust

[![crates.io][crate-badge]][crate-link]
[![Docs][docs-badge]][docs-link]
![Rust Version][rustc-image]

This crate provides an implementation of the [HpkeCrypto] trait using native Rust crypto implementations
([hkdf], [sha2], [p256], [p384], [x25519-dalek], [chacha20poly1305], [aes-gcm]).

Please see [hpke-rs] for more details.

[hkdf]: https://docs.rs/hkdf/
[sha2]: https://docs.rs/sha2
[p256]: https://docs.rs/p256
[p384]: https://docs.rs/p384
[x25519-dalek]: https://docs.rs/x25519-dalek
[chacha20poly1305]: https://docs.rs/chacha20poly1305
[aes-gcm]: https://docs.rs/aes-gcm
[hpkecrypto]: https://github.com/franziskuskiefer/hpke-rs/tree/main/traits
[rustc-image]: https://img.shields.io/badge/rustc-1.56+-blue.svg?style=for-the-badge
[docs-badge]: https://img.shields.io/badge/docs-rs-blue.svg?style=for-the-badge
[docs-link]: https://docs.rs/hpke-rs-rust-crypto
[crate-badge]: https://img.shields.io/crates/v/hpke-rs-rust-crypto.svg?style=for-the-badge
[crate-link]: https://crates.io/crates/hpke-rs-rust-crypto
[hpke-rs]: https://github.com/franziskuskiefer/hpke-rs
