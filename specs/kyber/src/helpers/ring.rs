use std::ops;

use crate::helpers::field::FieldElement;

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct PolynomialRingElement<const COEFFICIENT_MODULUS: u16, const COEFFICIENTS: usize> {
    pub coefficients: [FieldElement<COEFFICIENT_MODULUS>; COEFFICIENTS],
}

impl<const COEFFICIENT_MODULUS: u16, const COEFFICIENTS: usize> PolynomialRingElement<COEFFICIENT_MODULUS, COEFFICIENTS> {
    pub const ZERO: Self = Self {
        coefficients: [FieldElement::<COEFFICIENT_MODULUS>::ZERO; COEFFICIENTS],
    };
}

impl<const COEFFICIENT_MODULUS: u16, const COEFFICIENTS: usize> ops::Add for PolynomialRingElement<COEFFICIENT_MODULUS, COEFFICIENTS> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut result = PolynomialRingElement::<COEFFICIENT_MODULUS, COEFFICIENTS>::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = self.coefficients[i] + other.coefficients[i];
        }
        result
    }
}
impl<const COEFFICIENT_MODULUS: u16, const COEFFICIENTS: usize> ops::Sub for PolynomialRingElement<COEFFICIENT_MODULUS, COEFFICIENTS> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut result = PolynomialRingElement::<COEFFICIENT_MODULUS, COEFFICIENTS>::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = self.coefficients[i] - other.coefficients[i];
        }
        result
    }
}
