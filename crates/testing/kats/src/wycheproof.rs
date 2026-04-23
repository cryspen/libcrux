//! Wycheproof Known Answer Tests

pub mod schema_common;
pub use schema_common::TestResult;

#[cfg(feature = "chacha20poly1305")]
pub mod aead;

#[cfg(feature = "p256")]
pub mod ecdh;

#[cfg(feature = "ecdsa")]
pub mod ecdsa;

#[cfg(feature = "hkdf")]
pub mod hkdf;

#[cfg(feature = "hmac")]
pub mod mac;

#[cfg(feature = "mldsa")]
pub mod mldsa;

#[cfg(feature = "mlkem")]
pub mod mlkem;

#[cfg(feature = "curve25519")]
pub mod xdh;
