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
* As of commit [6d9d6de30f02e229dfc160323722c3ddac866181](https://github.com/C2SP/wycheproof/tree/6d9d6de30f02e229dfc160323722c3ddac866181)

The JSON files for ACVP ML-KEM and ML-DSA were taken from `https://github.com/usnistgov/ACVP-Server`
* As of commit [112690e8484dba7077709a05b1f3af58ddefdd5d](https://github.com/usnistgov/ACVP-Server/commit/112690e8484dba7077709a05b1f3af58ddefdd5d)
