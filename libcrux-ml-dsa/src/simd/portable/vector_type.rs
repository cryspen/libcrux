use crate::simd::traits::COEFFICIENTS_PER_VECTOR;

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i32;

#[derive(Clone, Copy)]
pub struct PortableVector {
    pub(crate) coefficients: [FieldElement; COEFFICIENTS_PER_VECTOR],
}

#[allow(non_snake_case)]
#[inline(always)]
pub fn ZERO() -> PortableVector {
    PortableVector {
        coefficients: [0i32; COEFFICIENTS_PER_VECTOR],
    }
}

#[inline(always)]
pub fn from_i32_array(array: &[i32]) -> PortableVector {
    PortableVector {
        coefficients: array[0..8].try_into().unwrap(),
    }
}

#[inline(always)]
pub fn to_i32_array(vector: PortableVector) -> [i32; 8] {
    vector.coefficients.try_into().unwrap()
}
