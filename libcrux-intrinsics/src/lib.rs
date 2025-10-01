//! Platform-specific SIMD intrinsics for libcrux.
//!
//! This crate provides SIMD intrinsics for ARM64 (128-bit) and x86_64 (256-bit) architectures.
//! It includes both real implementations for actual hardware and dummy implementations for extraction.

#![no_std]
#[cfg(all(feature = "simd128", not(hax)))]
pub mod arm64;
#[cfg(all(feature = "simd256", not(hax)))]
/// AVX2 intrinsics for x86_64 256-bit SIMD operations
pub mod avx2;

// When extracting F* we only want dummy files here.
#[cfg(all(feature = "simd128", hax))]
pub mod arm64_extract;
#[cfg(all(feature = "simd128", hax))]
pub use arm64_extract as arm64;

#[cfg(all(feature = "simd256", hax, pre_core_models))]
pub mod avx2_extract;
#[cfg(all(feature = "simd256", hax, pre_core_models))]
pub use avx2_extract as avx2;

#[cfg(all(feature = "simd256", hax, not(pre_core_models)))]
pub mod avx2;
