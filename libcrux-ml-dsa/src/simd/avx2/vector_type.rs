use super::SIMD_UNITS_IN_RING_ELEMENT;

pub(super) use libcrux_intrinsics::avx2::Vec256;

#[derive(Clone, Copy)]
pub struct AVX2SIMDUnit {
    pub(crate) coefficients: Vec256,
}

pub(crate) type AVX2RingElement = [Vec256; SIMD_UNITS_IN_RING_ELEMENT];

impl From<Vec256> for AVX2SIMDUnit {
    fn from(coefficients: Vec256) -> Self {
        Self { coefficients }
    }
}

pub(crate) fn zero() -> Vec256 {
    libcrux_intrinsics::avx2::mm256_setzero_si256()
}

#[allow(non_snake_case)]
pub(crate) fn ZERO() -> AVX2SIMDUnit {
    libcrux_intrinsics::avx2::mm256_setzero_si256().into()
}

pub(crate) fn from_coefficient_array(coefficient_array: &[i32]) -> Vec256 {
    libcrux_intrinsics::avx2::mm256_loadu_si256_i32(coefficient_array)
}

#[inline(always)]
pub(crate) fn to_coefficient_array(value: &Vec256, out: &mut [i32]) {
    libcrux_intrinsics::avx2::mm256_storeu_si256_i32(out, *value);
}
