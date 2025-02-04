//! A P-256 implementation.
//!
//! This crate should not be used directly and is internal to libcrux.
//! By default this crate is empty.

// HACL* generated code
mod p256;
mod p256_precomptable;

#[cfg(feature = "expose-hacl")]
pub use p256::*;
