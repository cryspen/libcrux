#![no_std]
#[cfg(all(feature = "simd128", not(hax)))]
pub mod arm64;
#[cfg(all(feature = "simd256", not(hax)))]
pub mod avx2;

// When extracting F* we only want dummy files here.
// sha3/aes stay on the trusted `arm64_extract` (bit_vec) intrinsics under
// `pre_core_models`; ml-kem/ml-dsa extract the real `arm64` (core-models) path.
#[cfg(all(feature = "simd128", hax, pre_core_models))]
pub mod arm64_extract;
#[cfg(all(feature = "simd128", hax, pre_core_models))]
pub use arm64_extract as arm64;

#[cfg(all(feature = "simd128", hax, not(pre_core_models)))]
pub mod arm64;

#[cfg(all(feature = "simd256", hax, pre_core_models))]
pub mod avx2_extract;
#[cfg(all(feature = "simd256", hax, pre_core_models))]
pub use avx2_extract as avx2;

#[cfg(all(feature = "simd256", hax, not(pre_core_models)))]
pub mod avx2;
