#![no_std]

mod arithmetic;
mod constants;
mod encoding;
mod hash_functions;
mod matrix;
mod ml_dsa_generic;
mod ntt;
mod polynomial;
mod pre_hash;
mod sample;
mod samplex4;
mod simd;
mod types;
mod utils;
// Public interface

pub use {
    ml_dsa_generic::{SigningError, VerificationError},
    types::*,
};

pub use crate::constants::KEY_GENERATION_RANDOMNESS_SIZE;
pub use crate::constants::SIGNING_RANDOMNESS_SIZE;

pub mod ml_dsa_44;
pub mod ml_dsa_65;
pub mod ml_dsa_87;
