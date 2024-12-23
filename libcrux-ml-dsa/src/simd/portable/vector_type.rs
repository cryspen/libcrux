use crate::simd::traits::COEFFICIENTS_IN_SIMD_UNIT;
/// Values having this type hold a representative 'x' of the ML-DSA field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i32;

#[derive(Clone, Copy)]
pub(crate) struct PortableSIMDUnit {
    pub(crate) coefficients: Coefficients,
}

pub(super) type Coefficients = [FieldElement; COEFFICIENTS_IN_SIMD_UNIT];

pub(crate) fn zero() -> Coefficients {
    [0i32; COEFFICIENTS_IN_SIMD_UNIT]
}

#[allow(non_snake_case)]
pub(crate) fn ZERO() -> PortableSIMDUnit {
    PortableSIMDUnit {
        coefficients: [0i32; COEFFICIENTS_IN_SIMD_UNIT],
    }
}

pub(crate) fn from_coefficient_array(array: &[i32]) -> Coefficients {
    array[0..8].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn to_coefficient_array(
    value: &Coefficients,
    out: &mut [i32], // len: COEFFICIENTS_IN_SIMD_UNIT
) {
    out.copy_from_slice(value);
}
