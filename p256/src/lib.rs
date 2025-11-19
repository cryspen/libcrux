//! A P-256 implementation.
//!
//! This crate should not be used directly and is internal to libcrux.
//! By default this crate is empty.
#![no_std]

// HACL* generated code
mod impl_kem;
mod p256;
mod p256_precomptable;

pub struct P256;

#[cfg(feature = "expose-hacl")]
pub use p256::*;
