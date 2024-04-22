use crate::arithmetic::MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS;
use crate::constants::FIELD_MODULUS;

#[cfg(feature = "simd128")]
pub(crate) type IntVec = super::intvec128::IntVec;

#[cfg(not(feature = "simd128"))]
pub(crate) type IntVec = super::intvec32::IntVec;

pub(crate) const SIZE_VEC: usize = 8;

#[cfg(feature = "simd128")]
pub(crate) use super::intvec128 as intvec;
#[cfg(not(feature = "simd128"))]
pub(crate) use super::intvec32 as intvec;
