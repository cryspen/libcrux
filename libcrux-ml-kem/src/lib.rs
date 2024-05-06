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
pub mod kyber1024;
pub mod kyber512;
pub mod kyber768;

pub use types::{MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey};

pub use ind_cca::{MlKemSharedSecret, ENCAPS_SEED_SIZE, KEY_GENERATION_SEED_SIZE};
