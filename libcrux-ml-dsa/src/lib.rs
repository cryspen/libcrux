#![no_std]

mod arithmetic;
mod constants;
mod encoding;
mod hash_functions;
mod instantiations;
mod matrix;
mod ml_dsa_generic;
mod ntt;
mod polynomial;
mod sample;
mod simd;
mod types;
mod utils;

// Public interface

pub use {ml_dsa_generic::VerificationError, types::*};

pub mod ml_dsa_44;
pub mod ml_dsa_65;
pub mod ml_dsa_87;
