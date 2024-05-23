//! # ML-KEM
//!
//! This crate implements all three ML-KEM variants 512, 768, and 1024.
//! It is formally verified using [hax] and [F*].
//!
//! ```
//! use rand::{rngs::OsRng, RngCore};
//!
//! // Ensure you use good randomness.
//! // It is not recommended to use OsRng directly!
//! // Instead it is highly encouraged to use RNGs like NISTs DRBG to account for
//! // bad system entropy.
//! fn random_array<const L: usize>() -> [u8; L] {
//!     let mut rng = OsRng;
//!     let mut seed = [0; L];
//!     rng.try_fill_bytes(&mut seed).unwrap();
//!     seed
//! }
//!
//! use libcrux_ml_kem::*;
//!
//! // This example use ML-KEM 768. The other variants can be used the same way.
//!
//! // Generate a key pair.
//! let randomness = random_array();
//! let key_pair = mlkem768::generate_key_pair(randomness);
//!
//! // Encapsulating a shared secret to a public key.
//! let randomness = random_array();
//! let (ciphertext, shared_secret) = mlkem768::encapsulate(key_pair.public_key(), randomness);
//!
//! // Decapsulating a shared secret with a private key.
//! let shared_secret_decapsulated = mlkem768::decapsulate(key_pair.private_key(), &ciphertext);
//! ```
//!
//! [hax]: https://cryspen.com/hax
//! [F*]: https://fstar-lang.org

#![no_std]
#![forbid(unsafe_code)]
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
mod invert_ntt;
mod matrix;
mod ntt;
mod polynomial;
mod sampling;
mod serialize;
mod types;
// Variants
pub mod mlkem1024;
pub mod mlkem512;
pub mod mlkem768;

#[path = "../../polynomials/src/lib.rs"]
pub mod libcrux_polynomials;

pub use constants::SHARED_SECRET_SIZE;
pub use ind_cca::{MlKemSharedSecret, ENCAPS_SEED_SIZE, KEY_GENERATION_SEED_SIZE};
// These types all have type aliases for the different variants.
pub use types::{MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey};
