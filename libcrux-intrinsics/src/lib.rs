#![no_std]
#![feature(extern_types)]

#[cfg(all(feature = "simd128", not(hax), not(eurydice)))]
pub mod arm64;
#[cfg(all(feature = "simd256", not(hax), not(eurydice)))]
pub mod avx2;

// When extracting F* or C we only want dummy files here.
#[cfg(all(feature = "simd128", any(hax, eurydice)))]
pub mod arm64_extract;
#[cfg(all(feature = "simd128", any(hax, eurydice)))]
pub use arm64_extract as arm64;
#[cfg(all(feature = "simd256", any(hax, eurydice)))]
pub mod avx2_extract;
#[cfg(all(feature = "simd256", any(hax, eurydice)))]
pub use avx2_extract as avx2;
