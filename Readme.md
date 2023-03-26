# libcrux - the formally verified crypto library

libcrux is a formally verified cryptographic library that brings together verified
artifacts from different sources.
It uses [hacspec] as a common language for the specifications underlying the
correctness and security proofs.

Please refer to the [Architecture] document for a detailed overview of the libcrux
architecture and properties and the [formal verification] directory for details
on the underlying formal proofs.

## Algorithms

> **Note**
> The available algorithms is still work in progress and will grow in future.

| Algorithm        | Platforms    |
| ---------------- | ------------ |
| AES              | x64 (AES-NI) |
| AES-GCM          | x64 (AES-NI) |
| Chacha20         | x64, arm64   |
| Poly1305         | x64, arm64   |
| Chacha20Poly1305 | x64, arm64   |
| Curve25519       | x64, arm64   |
| EdDSA 25519      | x64, arm64   |
| EcDSA P256       | x64, arm64   |
| Sha2             | x64, arm64   |
| Sha3             | x64, arm64   |
| Blake2           | x64, arm64   |
| HMAC             | x64, arm64   |
| HKDF             | x64, arm64   |
| Bls12-381        | x64, arm64   |
| HPKE             | x64, arm64   |

Other platforms might work as well but are not tested or optimized for at this point.

## Hardware support

The build enables all available hardware features for the target architecture.
Further, the library always performs runtime checks to ensure that the required
CPU features are available.

libcrux uses the following configurations for its hardware abstractions

- **simd128** assumes 128 bit SIMD instructions on the platform.
  This implies SSE3 and SSE4.1 on x64 CPUs and NEON on arm CPUs.
- **simd256** assumes 256 bit SIMD instructions on the platform
  This implies AVX and AVX2 on x64 CPUs.

## Randomness

libcrux provides a DRBG implementation that can be used standalone (`drbg::Drbg`)
or through the `Rng` traits.

[architecture]: ./Architecture.md
[hacspec]: https://hacspec.org
[formal verification]: ./formal_verification
