# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [v0.0.3-alpha.1]

- [#920](https://github.com/cryspen/libcrux/pull/920):
  - Drop support for XWingKyberDraft02, XWingKemDraft02, and X25519Kyber768Draft00
  - Add support for XWingKemDraft06
  - Add key gen and encaps derandomized functions
- [#922](https://github.com/cryspen/libcrux/pull/922): Make `no_std` optional using default `std` feature
