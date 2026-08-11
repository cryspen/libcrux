#![no_std]
#[cfg(all(feature = "simd128", not(hax)))]
pub mod arm64;
#[cfg(all(feature = "simd256", not(hax)))]
pub mod avx2;

// When extracting F* we choose per-ISA whether to route to the hand-written
// `*_extract` (bit_vec) stub or the differentially-tested core-models path.
// `pre_core_models` is a "both stub" alias (aes sets it); the per-ISA
// `pre_core_models_{arm64,avx2}` flags allow flipping one ISA independently
// (sha3 sets `pre_core_models_avx2` only: arm64 -> real core-models `Arm64`,
// avx2 -> the `Avx2_extract` bit_vec stub). ml-kem/ml-dsa set none -> real both.
#[cfg(all(feature = "simd128", hax, any(pre_core_models, pre_core_models_arm64)))]
pub mod arm64_extract;
#[cfg(all(feature = "simd128", hax, any(pre_core_models, pre_core_models_arm64)))]
pub use arm64_extract as arm64;

#[cfg(all(feature = "simd128", hax, not(any(pre_core_models, pre_core_models_arm64))))]
pub mod arm64;

#[cfg(all(feature = "simd256", hax, any(pre_core_models, pre_core_models_avx2)))]
pub mod avx2_extract;
#[cfg(all(feature = "simd256", hax, any(pre_core_models, pre_core_models_avx2)))]
pub use avx2_extract as avx2;

#[cfg(all(feature = "simd256", hax, not(any(pre_core_models, pre_core_models_avx2))))]
pub mod avx2;
