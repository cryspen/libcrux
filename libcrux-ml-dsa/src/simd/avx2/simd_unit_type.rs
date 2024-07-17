use crate::simd::traits::COEFFICIENTS_IN_SIMD_UNIT;

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i32;

#[derive(Clone, Copy)]
pub struct AVX2SIMDUnit {
    pub(crate) coefficients: [FieldElement; COEFFICIENTS_IN_SIMD_UNIT],
}

#[allow(non_snake_case)]
#[inline(always)]
pub fn ZERO() -> AVX2SIMDUnit {
    AVX2SIMDUnit {
        coefficients: [0i32; COEFFICIENTS_IN_SIMD_UNIT],
    }
}

#[inline(always)]
pub fn from_i32_array(array: &[i32]) -> AVX2SIMDUnit {
    AVX2SIMDUnit {
        coefficients: array[0..8].try_into().unwrap(),
    }
}

#[inline(always)]
pub fn to_i32_array(simd_unit: AVX2SIMDUnit) -> [i32; 8] {
    simd_unit.coefficients.try_into().unwrap()
}
