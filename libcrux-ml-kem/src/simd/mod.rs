pub(crate) mod simd_trait;

mod portable;

#[cfg(feature = "simd128")]
mod simd128;

#[cfg(feature = "simd256")]
mod simd256;
#[cfg(feature = "simd256")]
pub(crate) type Vector = simd256::SIMD256Vector;
