//! # Cryptographic Algorithms

#[cfg(feature = "aes_gcm")]
pub mod aes_gcm;

#[cfg(feature = "blake2")]
pub mod blake2;

#[cfg(feature = "chacha20_poly1305")]
pub mod chacha20poly1305;

#[cfg(feature = "curve25519")]
pub mod curve25519;

#[cfg(feature = "p256_ecdh")]
pub mod ecdh;

#[cfg(feature = "p256_ecdsa")]
pub mod ecdsa;

#[cfg(feature = "ed25519")]
pub mod ed25519;

#[cfg(feature = "sha2")]
pub mod sha2;

#[cfg(feature = "sha3")]
pub mod sha3;

#[cfg(feature = "hkdf")]
pub mod hkdf;

#[cfg(feature = "hmac")]
pub mod hmac;
