//! SIMD implementations of SHA3
//!
//! Runtime feature detection must be performed before calling these functions.
//!
//! If the caller does not perform feature detection, the top level functions
//! must be used.

#[cfg(any(feature = "simd128", hax))]
pub(crate) mod arm64;
#[cfg(any(feature = "simd256", hax))]
pub(crate) mod avx2;
