//! # libcrux
//!
//! The unified, formally verified, cryptography library.

pub use libcrux_platform::aes_ni_support;

// Jasmin
#[cfg(all(
    any(target_arch = "x86", target_arch = "x86_64"),
    any(target_os = "linux", target_os = "macos")
))]
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
