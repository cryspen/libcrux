//! # libcrux
//!
//! The unified, formally verified, cryptography library.

pub(crate) mod hw_detection;
pub use hw_detection::aes_ni_support;

// Jasmin
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub(crate) mod jasmin;

// libcrux
pub mod aead;
pub mod bls12;
pub mod digest;
pub mod drbg;
pub mod ecdh;
pub mod hkdf;
pub mod hmac;
pub mod hpke;
pub mod kem;
pub mod signature;

// XXX: temporary hacspec lib
pub(crate) mod hacspec_lib;

// hacspec utils
#[cfg(feature = "hacspec")]
pub(crate) mod specs;

/// Re-export hacspec functions with the hacspec feature.
#[cfg(feature = "hacspec")]
pub use hacspec_lib::prelude::*;
