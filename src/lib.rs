//! # libcrux
//!
//! The unified, formally verified, cryptography library.

pub use libcrux_platform::aes_ni_support;

// Jasmin
#[cfg(all(
    libjade,
    target_arch = "x86_64",
    any(target_os = "linux", target_os = "macos")
))]
pub(crate) mod jasmin;

// HACL
pub(crate) mod hacl;

// libcrux
pub mod aead;
// The BLS code requires a 64 bit system.
#[cfg(all(not(target_arch = "wasm32"), not(target_arch = "x86")))]
// Generated code: don't let clippy touch it.
#[allow(clippy::all)]
pub mod bls12;
pub mod digest;
// XXX: Looks like the bindings are broken for drbg for some reason.
#[cfg(not(target_arch = "wasm32"))]
pub mod drbg;
pub mod ecdh;
pub mod hkdf;
pub mod hmac;
// hacspec code: don't let clippy touch it.
#[allow(clippy::all)]
pub mod hpke;
pub mod kem;
pub mod signature;

#[cfg(all(target_arch = "wasm32", feature = "wasm"))]
pub mod wasm;
