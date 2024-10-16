//! # Polynomials for libcrux
//!
//! This crate abstracts efficient implementations of polynomials for algorithms
//! such as ML-KEM and ML-DSA.
//!
//! The crate only defines a common API.
//! The actual implementations are in separate crates for different platforms for
//! performance reasons.

pub(crate) use libcrux_traits::Operations;

// There's no runtime detection here. This either exposes the real SIMD vector,
// or the portable when the feature is not set.
//
// The consumer needs to use runtime feature detection and the appropriate vector
// in each case.
#[cfg(feature = "simd128")]
mod neon;
#[cfg(feature = "simd256")]
pub(crate) use libcrux_avx2::SIMD256Vector;
#[cfg(feature = "simd128")]
pub(crate) use neon::SIMD128Vector;

pub(crate) mod portable;

pub(crate) fn montgomery_multiply_fe<T: Operations>(v: T, fer: i16) -> T {
    T::montgomery_multiply_by_constant(v, fer)
}
pub(crate) fn to_standard_domain<T: Operations>(v: T) -> T {
    T::montgomery_multiply_by_constant(v, portable::MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS as i16)
}

pub(crate) fn to_unsigned_representative<T: Operations>(a: T) -> T {
    let t = T::shift_right::<15>(a);
    let fm = T::bitwise_and_with_constant(t, portable::FIELD_MODULUS);
    T::add(a, &fm)
}

pub(crate) fn decompress_1<T: Operations>(v: T) -> T {
    T::bitwise_and_with_constant(T::sub(T::ZERO(), &v), 1665)
}
