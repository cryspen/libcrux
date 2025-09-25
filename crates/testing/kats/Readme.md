# KATs

This crate provides KAT test vectors for:
- ML-DSA (wycheproof)
    - sign (`noseed`)
    - verify
- ML-KEM (wycheproof)
    - keygen/decaps
    - encaps

⚠️ NOTE: This crate serves as an internal testing dependency for other `libcrux`
crates, and is not intended to be used directly.

## Source

The JSON files for ML-KEM and ML-DSA were taken from `https://github.com/C2SP/wycheproof`
* As of commit [cd136e97040de0842c3a198670b1c5e4f423c940](https://github.com/C2SP/wycheproof/tree/cd136e97040de0842c3a198670b1c5e4f423c940)
