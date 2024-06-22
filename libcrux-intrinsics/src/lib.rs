// #[cfg(all(feature = "simd128", not(eurydice), not(hax)))]
#[cfg(feature = "simd128")]
pub mod arm64;
// #[cfg(all(feature = "simd256", not(eurydice), not(hax)))]
#[cfg(feature = "simd256")]
pub mod avx2;

#[cfg(feature = "wasm")]
pub mod wasm;

// // When extracting C or F* we only want dummy files here.
// #[cfg(all(feature = "simd128", any(eurydice, hax)))]
// pub mod arm64_extract;
// #[cfg(all(feature = "simd128", any(eurydice, hax)))]
// pub use arm64_extrat as arm64;
// #[cfg(all(feature = "simd256", any(eurydice, hax)))]
// pub mod avx2_extract;
// #[cfg(all(feature = "simd256", any(eurydice, hax)))]
// pub use avx2_extract as avx2;
