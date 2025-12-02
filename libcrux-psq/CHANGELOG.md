# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- [#1248](https://github.com/cryspen/libcrux/pull/1248):
    - Add signature-based authentication (breaking because ciphersuite IDs have changed)
    - Add AES-GCM 128 ciphersuite support
    - Add secret export API to `Session`
    - Add support for retrieving initiator authenticator mid-handshake from Responder
    - Update `Session` serialization API to accept initiator authenticator instead of initiator DH public key only (breaking)

## [0.0.5] (2025-11-05)

- [#1108](https://github.com/cryspen/libcrux/pull/1108): Allow using Classic McEliece for PQ KEM
- [#1091](https://github.com/cryspen/libcrux/pull/1091): Allow derivation of an Unregistered PSK
- [#1081](https://github.com/cryspen/libcrux/pull/1081): Session storage
- [#1079](https://github.com/cryspen/libcrux/pull/1079): Use TLSCodec for Serialization/Deserialization in PSQv1
- [#1048](https://github.com/cryspen/libcrux/pull/1048): PSQv2
