# Release

## Update version

Initially, all crate versions in this repository were in sync, but we moved away from that model.
Now, a crate _may_ follow the workspace version, but is not required to.

Change the workspace version with

`cargo release version <LEVEL> --execute`

Change the version of an individual crate with

`cargo release -p <CRATE> version <LEVEL>`

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

### Independently Versioned

- blake2
