#![no_std]
#[cfg(all(feature = "simd128", not(hax)))]
pub mod arm64;
#[cfg(all(feature = "simd256", not(hax)))]
pub mod avx2;

// When extracting F* we only want dummy files here.
#[cfg(all(feature = "simd128", hax))]
pub mod arm64_extract;
#[cfg(all(feature = "simd128", hax))]
pub use arm64_extract as arm64;
#[cfg(all(feature = "simd256", hax))]
pub mod avx2_extract;
#[cfg(all(feature = "simd256", hax))]
pub use avx2_extract as avx2;

#[cfg(feature = "simd128")]
pub mod arm64_secret;
#[cfg(feature = "simd256")]
pub mod avx2_secret;