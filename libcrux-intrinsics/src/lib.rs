#[cfg(all(feature = "simd128", not(eurydice), not(hax)))]
pub mod arm64;
#[cfg(all(feature = "simd256", not(eurydice), not(hax)))]
pub mod avx2;

// When extracting C or F* we only want dummy files here.
#[cfg(all(feature = "simd128", any(eurydice, hax)))]
pub mod arm64_extract;
#[cfg(all(feature = "simd128", any(eurydice, hax)))]
pub use arm64_extract as arm64;
#[cfg(all(feature = "simd256", any(eurydice, hax)))]
pub mod avx2_extract;
#[cfg(all(feature = "simd256", any(eurydice, hax)))]
pub use avx2_extract as avx2;
