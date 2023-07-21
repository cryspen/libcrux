use std::ops;

use crate::helpers::field::FieldElement;

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct PolynomialRingElement<F: FieldElement, const COEFFICIENTS: usize> {
    pub coefficients: [F; COEFFICIENTS],
}

impl<F: FieldElement, const COEFFICIENTS: usize> PolynomialRingElement<F, COEFFICIENTS>
{
    pub const ZERO: Self = Self {
        coefficients: [F::ZERO; COEFFICIENTS],
    };
}

impl<F: FieldElement, const COEFFICIENTS: usize> ops::Add for PolynomialRingElement<F, COEFFICIENTS> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut result = PolynomialRingElement::<F, COEFFICIENTS>::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = self.coefficients[i] + other.coefficients[i];
        }
        result
    }
}
impl<F: FieldElement, const COEFFICIENTS: usize> ops::Sub for PolynomialRingElement<F, COEFFICIENTS> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut result = PolynomialRingElement::<F, COEFFICIENTS>::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = self.coefficients[i] - other.coefficients[i];
        }
        result
    }
}
