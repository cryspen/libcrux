use super::vector_type::*;
use crate::vector::traits::COEFFICIENTS_PER_VECTOR;

#[inline(always)]
pub fn add(mut lhs: PortableVector, rhs: &PortableVector) -> PortableVector {
    for i in 0..COEFFICIENTS_PER_VECTOR {
        lhs.coefficients[i] += rhs.coefficients[i];
    }

    lhs
}

#[inline(always)]
pub fn subtract(mut lhs: PortableVector, rhs: &PortableVector) -> PortableVector {
    for i in 0..COEFFICIENTS_PER_VECTOR {
        lhs.coefficients[i] -= rhs.coefficients[i];
    }

    lhs
}
