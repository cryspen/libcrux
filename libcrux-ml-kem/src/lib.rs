//! # ML-KEM
//!
//! This crate implements all three ML-KEM variants 512, 768, and 1024.
//! It is formally verified using [hax] and [F*].
//!
//! [hax]: https://cryspen.com/hax
//! [F*]: https://fstar-lang.org

#![no_std]
#![forbid(unsafe_code, missing_docs)]
#![warn(rust_2018_idioms, unused_lifetimes, unused_qualifications)]
#![allow(clippy::needless_range_loop)]

pub(crate) mod hax_utils;

// This module is declared here since otherwise, hax reports the following error:
//
// The THIR body of item
// DefId(0:986 ~ libcrux[92b3]::kem::kyber768::parameters::COEFFICIENTS_IN_RING_ELEMENT)
// was stolen.
//
// This is being tracked in https://github.com/hacspec/hacspec-v2/issues/27
pub(crate) mod constants;

/// Helpers for verification and extraction
mod helper;

mod constant_time_ops;
mod hash_functions;
mod ind_cca;
mod ind_cpa;
mod matrix;
mod polynomial;
mod sampling;
mod serialize;
mod types;
// Variants
pub mod mlkem1024;
pub mod mlkem512;
pub mod mlkem768;

pub use constants::SHARED_SECRET_SIZE;
pub use ind_cca::{MlKemSharedSecret, ENCAPS_SEED_SIZE, KEY_GENERATION_SEED_SIZE};
// These types all have type aliases for the different variants.
pub use types::{MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey};
