# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.7.0-pre.1] (2026-07-13)

### Added

- [#147](https://github.com/celabshq/hpke-rs/pull/147): Add P384 and P521 DHKEM support for the libcrux provider via RustCrypto crates guarded behind the `libcrux-rustcrypto-p-curves` feature flag.
- [#146](https://github.com/celabshq/hpke-rs/pull/146): Add support for ML-KEM768 and ML-KEM1024 gated behind the `draft-connolly-cfrg-hpke-mlkem` feature flag.

### Changed

- [#XYZ](https://github.com/celabshq/libcrux/pull/XYZ): Update dependencies: `hpke-rs-crypto`, `libcrux-traits`, `libcrux-aead`, `libcrux-hkdf`, `libcrux-kem`

## [0.6.1] - 2026-02-20

### Changed
- [#129](https://github.com/cryspen/hpke-rs/pull/129): Update libcrux dependencies
- [#122](https://github.com/cryspen/hpke-rs/pull/122): Update rand dependencies

## [0.5.1] - 2026-02-02

- [#114](https://github.com/celabshq/libcrux/pull/114): Update dependencies `libcrux-ecdh`, `libcrux-aead`, `libcrux-sha3`, `libcrux-kem`, `libcrux-hkdf`, `libcrux-traits`

## [0.5.0] - 2025-12-16

- [#105](https://github.com/cryspen/hpke-rs/pull/105) Update dependencies

## 0.4.0 - 2025-12-01

- [#98](https://github.com/cryspen/hpke-rs/pull/98): add support for AES-GCM to the provider

## 0.3.0 - 2025-07-01

* initial release

*Please disregard any previous versions.*
