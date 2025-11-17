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
