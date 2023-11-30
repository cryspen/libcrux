# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.0] - 2023-12-01

- [#59](https://github.com/franziskuskiefer/hpke-rs/pull/59): hpke-rs-rust-crypto: make deterministic-prng enable the std feature
- [#56](https://github.com/franziskuskiefer/hpke-rs/pull/56): CI: check no-std support
- [#58](https://github.com/franziskuskiefer/hpke-rs/pull/58): no-std-ify hpke-rs-rust-crypto (some more)
- [#57](https://github.com/franziskuskiefer/hpke-rs/pull/57): switch from x25519-dalek-ng to x25519-dalek
- [#55](https://github.com/franziskuskiefer/hpke-rs/pull/55): rm `RwLock` from `Hpke` and no-std-ify the `hpke-rs` library
- [#53](https://github.com/franziskuskiefer/hpke-rs/pull/53): rm getrandom dep
- [#50](https://github.com/franziskuskiefer/hpke-rs/pull/50): no-std-ify hpke-rs-crypto
- [#49](https://github.com/franziskuskiefer/hpke-rs/pull/49): hpke-rs-crypto: make serde opt-in
- [#48](https://github.com/franziskuskiefer/hpke-rs/pull/48): no-std-ify hpke-rs-rust-crypto
- [#47](https://github.com/franziskuskiefer/hpke-rs/pull/47): hpks-rs-crypto: simplify Cargo.toml

## [0.1.2] - 2023-11-21

- Updated TLS codec dependency
- [#44](https://github.com/franziskuskiefer/hpke-rs/pull/44): implement std::error::Error for HpkeError

## [0.1.1] - 2023-06-22

### Changed

- Updated crypto providers
- Use variable length TLS encoding as required by TLS for serialization
