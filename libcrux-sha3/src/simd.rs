//! SIMD implementations of SHA3
//!
//! Runtime feature detection must be performed before calling these functions.
//!
//! If the caller does not perform feature detection, the top level functions
//! must be used.

#[cfg(feature = "simd128")]
mod arm64;
#[cfg(feature = "simd256")]
mod avx2;
