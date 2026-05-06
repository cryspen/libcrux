# KATs

This crate provides KAT test vectors for:
- ML-DSA (wycheproof)
    - sign (`noseed`)
    - verify
- ML-DSA (acvp)
    - keygen
    - sign
    - verify
- ML-KEM (wycheproof)
    - keygen/decaps
    - encaps

⚠️ NOTE: This crate serves as an internal testing dependency for other `libcrux`
crates, and is not intended to be used directly.

## Source

The JSON files for wycheproof ML-KEM and ML-DSA were taken from `https://github.com/C2SP/wycheproof`
* As of commit [cd136e97040de0842c3a198670b1c5e4f423c940](https://github.com/C2SP/wycheproof/tree/cd136e97040de0842c3a198670b1c5e4f423c940)

The JSON files for ACVP ML-KEM and ML-DSA were taken from `https://github.com/usnistgov/ACVP-Server`
* As of commit [112690e8484dba7077709a05b1f3af58ddefdd5d](https://github.com/usnistgov/ACVP-Server/commit/112690e8484dba7077709a05b1f3af58ddefdd5d)

The RSP files for SHA-2 were taken from NISTs [Cryptographic Algorithm Validation Program](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing) (accessed 05.05.2026).

The test vectors for poly1305 are taken from [boringssl](https://github.com/google/boringssl/blob/2a8e86174536b735a777a56897c7949d33bd46a6/crypto/poly1305/poly1305_tests.txt).
