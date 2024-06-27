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

#[cfg(feature = "std")]
extern crate std;

pub(crate) mod hax_utils;

// This module is declared here since otherwise, hax reports the following error:
//
// The THIR body of item
// DefId(0:986 ~ libcrux[92b3]::kem::kyber768::parameters::COEFFICIENTS_IN_RING_ELEMENT)
// was stolen.
//
// This is being tracked in https://github.com/hacspec/hacspec-v2/issues/27
#[cfg(feature = "pre-verification")]
pub(crate) mod constants;

/// Helpers for verification and extraction
#[cfg(feature = "pre-verification")]
mod helper;
#[cfg(feature = "pre-verification")]
mod utils;

#[cfg(feature = "pre-verification")]
mod constant_time_ops;
#[cfg(feature = "pre-verification")]
mod hash_functions;
#[cfg(feature = "pre-verification")]
mod ind_cca;
#[cfg(feature = "pre-verification")]
mod ind_cpa;
#[cfg(feature = "pre-verification")]
mod invert_ntt;

#[cfg(feature = "pre-verification")]
mod matrix;
#[cfg(feature = "pre-verification")]
mod ntt;
#[cfg(feature = "pre-verification")]
mod polynomial;
#[cfg(feature = "pre-verification")]
mod sampling;
#[cfg(feature = "pre-verification")]
mod serialize;
#[cfg(feature = "pre-verification")]
mod types;
#[cfg(feature = "pre-verification")]
mod vector;


#[cfg(not(feature = "pre-verification"))]
mod kem;
// Variants
#[cfg(all(feature = "mlkem1024", feature = "pre-verification"))]
pub mod mlkem1024;
#[cfg(all(feature = "mlkem512", feature = "pre-verification"))]
pub mod mlkem512;
#[cfg(all(feature = "mlkem768", feature = "pre-verification"))]
pub mod mlkem768;


// Variants
#[cfg(all(feature = "mlkem512", not(feature = "pre-verification")))]
pub mod mlkem512 {
    pub use crate::kem::kyber::kyber512::*;
}

#[cfg(all(feature = "mlkem768", not(feature = "pre-verification")))]
pub mod mlkem768 {
    pub use crate::kem::kyber::kyber768::*;
}

#[cfg(all(feature = "mlkem1024", not(feature = "pre-verification")))]
pub mod mlkem1024 {
    pub use crate::kem::kyber::kyber1024::*;
}

#[cfg(all(feature = "kyber", feature = "pre-verification"))]
pub mod kyber512 {
    //! Kyber 512 (NIST PQC Round 3)
    pub use crate::mlkem512::generate_key_pair;
    pub use crate::mlkem512::kyber::decapsulate;
    pub use crate::mlkem512::kyber::encapsulate;
    pub use crate::mlkem512::validate_public_key;
}

#[cfg(all(feature = "kyber", feature = "pre-verification"))]
pub mod kyber768 {
    //! Kyber 768 (NIST PQC Round 3)
    pub use crate::mlkem768::generate_key_pair;
    pub use crate::mlkem768::kyber::decapsulate;
    pub use crate::mlkem768::kyber::encapsulate;
    pub use crate::mlkem768::validate_public_key;
}

#[cfg(all(feature = "kyber", feature = "pre-verification"))]
pub mod kyber1024 {
    //! Kyber 1024 (NIST PQC Round 3)
    pub use crate::mlkem1024::generate_key_pair;
    pub use crate::mlkem1024::kyber::decapsulate;
    pub use crate::mlkem1024::kyber::encapsulate;
    pub use crate::mlkem1024::validate_public_key;
}

#[cfg(feature = "pre-verification")]
pub use constants::SHARED_SECRET_SIZE;
#[cfg(not(feature = "pre-verification"))]
pub const SHARED_SECRET_SIZE: usize = kem::kyber::constants::SHARED_SECRET_SIZE;

#[cfg(feature = "pre-verification")]
pub use ind_cca::{MlKemSharedSecret, ENCAPS_SEED_SIZE, KEY_GENERATION_SEED_SIZE};
#[cfg(not(feature = "pre-verification"))]
pub use kem::kyber::MlKemSharedSecret;
#[cfg(not(feature = "pre-verification"))]
pub const ENCAPS_SEED_SIZE: usize = kem::kyber::constants::SHARED_SECRET_SIZE;
#[cfg(not(feature = "pre-verification"))]
pub const KEY_GENERATION_SEED_SIZE: usize = kem::kyber::KEY_GENERATION_SEED_SIZE;

// These types all have type aliases for the different variants.
#[cfg(not(feature = "pre-verification"))]
pub use kem::kyber::{MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey};
#[cfg(feature = "pre-verification")]
pub use types::{MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey};
