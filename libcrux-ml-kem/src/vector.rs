//! # Polynomials for libcrux
//!
//! This crate abstracts efficient implementations of polynomials for algorithms
//! such as ML-KEM and ML-DSA.
//!
//! The crate only defines a common API.
//! The actual implementations are in separate crates for different platforms for
//! performance reasons.
//!
//! FIXME: This is kyber specific for now.

pub(crate) mod traits;
use traits::INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;

pub(crate) use traits::{
    decompress_1, montgomery_multiply_fe, to_standard_domain, to_unsigned_representative,
    Operations, FIELD_ELEMENTS_IN_VECTOR, FIELD_MODULUS,
};

// XXX: This is not used on neon right now
#[cfg(feature = "simd256")]
pub(crate) mod rej_sample_table;

// There's no runtime detection here. This either exposes the real SIMD vector,
// or the portable when the feature is not set.
//
// The consumer needs to use runtime feature detection and the appropriate vector
// in each case.
#[cfg(feature = "simd128")]
mod neon;
#[cfg(feature = "simd128")]
pub(crate) use neon::SIMD128Vector;
#[cfg(feature = "simd256")]
mod avx2;
#[cfg(feature = "simd256")]
pub(crate) use avx2::SIMD256Vector;

pub mod portable;
