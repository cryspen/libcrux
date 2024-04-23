pub(crate) mod simd_trait;

#[cfg(feature = "simd128")]
mod portable;
#[cfg(feature = "simd128")]
mod simd128;
#[cfg(feature = "simd128")]
pub(crate) type Vector = simd128::SIMD128Vector;

#[cfg(not(feature = "simd128"))]
mod portable;
#[cfg(not(feature = "simd128"))]
pub(crate) type Vector = portable::PortableVector;
