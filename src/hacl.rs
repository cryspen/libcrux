//! # Low-level HACL APIs
//!
//! Unsafe API for HACL.
//!
//! |             | x86 | x86-64             | Arm32 | Arm64 | s390x |
//! | ----------- | --- | ------------------ | ----- | ----- | ----- |
//! | Portable C  | ✓   | ✓                  | ✓     | ✓     | ✓     |
//! | simd128     | -   | SSE2, SSE3, SSE4.1 | -     | NEON  | z14   |
//! | simd256     | -   | AVX, AVX2          | -     | -     | -     |

#[cfg(aes_ni)]
pub(crate) mod aesgcm;
pub(crate) mod blake2;
pub(crate) mod chacha20_poly1305;
pub(crate) mod curve25519;
#[cfg(not(target_arch = "wasm32"))]
pub(crate) mod drbg;
pub(crate) mod ed25519;
pub(crate) mod hkdf;
pub(crate) mod hmac;
pub(crate) mod p256;
pub(crate) mod sha2;
pub(crate) mod sha3;

/// Unified error type.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    ChaCha20Poly1305(chacha20_poly1305::Error),
    Curve25519(curve25519::Error),
    P256(p256::Error),
    Ed25519(ed25519::Error),
    Hkdf(hkdf::Error),
}

impl From<chacha20_poly1305::Error> for Error {
    fn from(val: chacha20_poly1305::Error) -> Self {
        Error::ChaCha20Poly1305(val)
    }
}

impl From<curve25519::Error> for Error {
    fn from(val: curve25519::Error) -> Self {
        Error::Curve25519(val)
    }
}

impl From<p256::Error> for Error {
    fn from(val: p256::Error) -> Self {
        Error::P256(val)
    }
}

impl From<hkdf::Error> for Error {
    fn from(val: hkdf::Error) -> Self {
        Error::Hkdf(val)
    }
}

impl From<ed25519::Error> for Error {
    fn from(val: ed25519::Error) -> Self {
        Error::Ed25519(val)
    }
}
