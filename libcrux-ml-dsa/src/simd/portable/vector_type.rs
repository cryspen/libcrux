use crate::simd::traits::COEFFICIENTS_IN_SIMD_UNIT;
/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i32;

#[derive(Clone, Copy)]
pub struct PortableSIMDUnit {
    pub(crate) coefficients: [FieldElement; COEFFICIENTS_IN_SIMD_UNIT],
}

#[allow(non_snake_case)]
pub(crate) fn ZERO() -> PortableSIMDUnit {
    PortableSIMDUnit {
        coefficients: [0i32; COEFFICIENTS_IN_SIMD_UNIT],
    }
}

pub(crate) fn from_coefficient_array(array: &[i32]) -> PortableSIMDUnit {
    PortableSIMDUnit {
        coefficients: array[0..8].try_into().unwrap(),
    }
}

pub(crate) fn to_coefficient_array(x:&PortableSIMDUnit) -> [i32; 8] {
    x.coefficients
}