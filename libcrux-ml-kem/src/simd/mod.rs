pub(crate) mod simd_trait;

#[cfg(all(not(feature = "simd128"), not(feature = "simd256")))]
mod portable;
#[cfg(all(not(feature = "simd128"), not(feature = "simd256")))]
pub(crate) type Vector = portable::PortableVector;

#[cfg(feature = "simd128")]
mod portable; 
#[cfg(feature = "simd128")]
mod simd128;
#[cfg(feature = "simd128")]
pub(crate) type Vector = simd128::SIMD128Vector;

#[cfg(feature = "simd256")]
mod portable;
#[cfg(feature = "simd256")]
mod simd256;
#[cfg(feature = "simd256")]
pub(crate) type Vector = simd256::SIMD256Vector;
