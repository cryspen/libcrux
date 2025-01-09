//! # ML-KEM
//!
//! This crate implements all three ML-KEM variants 512, 768, and 1024. It is
//! formally verified using [hax](https://cryspen.com/hax) and
//! [F*](https://fstar-lang.org).
//!
//! Functions in this crate use CPU feature detection to pick the most efficient version
//! on each platform. To use a specific version with your own feature detection
//! use e.g. one of the following
//! - `mlkem768::avx2::generate_key_pair`,
//! - `mlkem768::neon::generate_key_pair`,
//! - `mlkem768::portable::generate_key_pair`,
//!
//! analogously for encapsulation and decapsulation."
#![cfg_attr(
    feature = "mlkem768",
    doc = r##"
```
 use rand::{rngs::OsRng, RngCore};

 // Ensure you use good randomness.
 // It is not recommended to use OsRng directly!
 // Instead it is highly encouraged to use RNGs like NISTs DRBG to account for
 // bad system entropy.
 fn random_array<const L: usize>() -> [u8; L] {
     let mut rng = OsRng;
     let mut seed = [0; L];
     rng.try_fill_bytes(&mut seed).unwrap();
     seed
 }

 use libcrux_ml_kem::*;

 // This example uses ML-KEM 768. The other variants can be used the same way.

 // Generate a key pair.
 let key_pair = {
    let randomness = random_array();
    mlkem768::generate_key_pair(randomness)
 };

 // Encapsulating a shared secret to a public key.
 let (ciphertext, shared_secret) = {
    let randomness = random_array();
    mlkem768::encapsulate(key_pair.public_key(), randomness)
 };

 // Decapsulating a shared secret with a private key.
 let shared_secret_decapsulated = mlkem768::decapsulate(key_pair.private_key(), &ciphertext);

 assert_eq!(shared_secret_decapsulated, shared_secret);
```"##
)]
//!
//! ## Features
//!
//! By default, all ML-KEM parameter sets are enabled. If required, they are
//! available individually under feature flags `mlkem512`, `mlkem768`,
//! `mlkem1024`.
//!
//! ### Kyber Round 3
//! The `kyber` flag also gives access to an, as yet, unverified implementation
//! of Kyber as submitted in Round 3 of the NIST PQ competition.
//!

#![no_std]
#![deny(missing_docs)]
#![deny(unsafe_code)]
#![warn(rust_2018_idioms, unused_lifetimes, unused_qualifications)]
#![allow(clippy::needless_range_loop)]
#![warn(missing_docs)]
// Enable doc cfg feature for doc builds. They use nightly.
#![cfg_attr(doc_cfg, feature(doc_cfg))]

#[cfg(feature = "std")]
extern crate std;

/// Feature gating helper macros
#[macro_use]
mod cfg;

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
mod mlkem;
mod ntt;
mod polynomial;
mod sampling;
mod serialize;
mod types;
mod utils;
mod variant;
pub mod vector;

/// Public ML-KEM API.
pub use mlkem::*;

// #[cfg(feature = "mlkem512")]
// #[cfg_attr(docsrs, doc(cfg(feature = "mlkem512")))]
// pub mod mlkem512;

// #[cfg(feature = "mlkem768")]
// #[cfg_attr(docsrs, doc(cfg(feature = "mlkem768")))]
// pub mod mlkem768;

// #[cfg(feature = "mlkem1024")]
// #[cfg_attr(docsrs, doc(cfg(feature = "mlkem1024")))]
// pub mod mlkem1024;

pub use constants::SHARED_SECRET_SIZE;

pub use ind_cca::{MlKemSharedSecret, ENCAPS_SEED_SIZE, KEY_GENERATION_SEED_SIZE};

// These types all have type aliases for the different variants.
pub use types::{MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey};

// cfg_kyber! {
//     #[cfg(feature = "mlkem512")]
//     #[cfg_attr(docsrs, doc(cfg(all(feature = "kyber", feature = "mlkem512"))))]
//     pub mod kyber512 {
//         //! Kyber 512 (NIST PQC Round 3)
//         cfg_no_eurydice! {
//             pub use crate::mlkem512::kyber::generate_key_pair;
//             pub use crate::mlkem512::kyber::decapsulate;
//             pub use crate::mlkem512::kyber::encapsulate;
//             pub use crate::mlkem512::validate_public_key;
//             pub use crate::mlkem512::validate_private_key;
//         }
//     }

//     #[cfg(feature = "mlkem768")]
//     #[cfg_attr(docsrs, doc(cfg(all(feature = "kyber", feature = "mlkem768"))))]
//     pub mod kyber768 {
//         //! Kyber 768 (NIST PQC Round 3)
//         cfg_no_eurydice! {
//             pub use crate::mlkem768::kyber::generate_key_pair;
//             pub use crate::mlkem768::kyber::decapsulate;
//             pub use crate::mlkem768::kyber::encapsulate;
//             pub use crate::mlkem768::validate_public_key;
//             pub use crate::mlkem768::validate_private_key;
//         }
//     }

//     #[cfg(feature = "mlkem1024")]
//     #[cfg_attr(docsrs, doc(cfg(all(feature = "kyber", feature = "mlkem1024"))))]
//     pub mod kyber1024 {
//         //! Kyber 1024 (NIST PQC Round 3)
//         cfg_no_eurydice! {
//             pub use crate::mlkem1024::kyber::generate_key_pair;
//             pub use crate::mlkem1024::kyber::decapsulate;
//             pub use crate::mlkem1024::kyber::encapsulate;
//             pub use crate::mlkem1024::validate_public_key;
//             pub use crate::mlkem1024::validate_private_key;
//         }
//     }
// }
