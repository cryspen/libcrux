//! A P-256 implementation.
//!
//! This crate should not be used directly and is internal to libcrux.
//! By default this crate is empty.
#![no_std]

// The two kinds of data that are actually there
const SCALAR_LEN: usize = 32;
const POINT_LEN: usize = 64;

pub mod ecdh_api;
mod impl_kem;

// HACL* generated code
pub(crate) mod p256;
mod p256_precomptable;

pub struct P256;

#[cfg(feature = "expose-hacl")]
pub use p256::*;
