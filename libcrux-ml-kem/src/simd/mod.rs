pub(crate) mod simd_trait;

pub(crate) mod portable;

#[cfg(feature = "simd128")]
pub(crate) mod simd128;

#[cfg(feature = "simd256")]
pub(crate) mod simd256;
#[cfg(feature = "simd256")]
pub(crate) type Vector = simd256::SIMD256Vector;
