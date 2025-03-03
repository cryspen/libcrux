# Release

## Update version
All versions in this repository are in sync right now, for better or worse.

Change the version with

`cargo release version <LEVEL> --execute`

## Crates

Main crate: `libcrux`

Crates that can be used directly
- blake2
- sha2
- sha3
- ml-dsa
- ml-kem
- chacha20poly1305
- hkdf
- hmac
- curve25519
- ecdsa
- ed25519
- rsa

Additional protocols
- psq

Higher level crates
- ecdh
- kem

### Utility crates
- hacl-rs
- traits
- macros
- poly1305
- p256

### Other libraries
- sys/libjade

### Legacy
- sys/hacl
