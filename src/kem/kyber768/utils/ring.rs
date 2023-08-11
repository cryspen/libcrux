use std::ops::{self, Index, IndexMut};

use crate::kem::kyber768::utils::field::FieldElement;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PolynomialRingElement<F: FieldElement, const COEFFICIENTS: usize> {
    pub(crate) coefficients: [F; COEFFICIENTS],
}

impl<F: FieldElement, const COEFFICIENTS: usize> PolynomialRingElement<F, COEFFICIENTS> {
    pub const ZERO: Self = Self {
        coefficients: [F::ZERO; COEFFICIENTS],
    };

    pub fn new(coefficients: [F; COEFFICIENTS]) -> Self {
        Self { coefficients }
    }

    pub fn coefficients(&self) -> &[F; COEFFICIENTS] {
        &self.coefficients
    }

    pub fn len(&self) -> usize {
        self.coefficients.len()
    }
}

impl<F: FieldElement, const COEFFICIENTS: usize> Index<usize>
    for PolynomialRingElement<F, COEFFICIENTS>
{
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        &self.coefficients[index]
    }
}

impl<F: FieldElement, const COEFFICIENTS: usize> IndexMut<usize>
    for PolynomialRingElement<F, COEFFICIENTS>
{
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.coefficients[index]
    }
}

impl<F: FieldElement, const COEFFICIENTS: usize> IntoIterator
    for PolynomialRingElement<F, COEFFICIENTS>
{
    type Item = F;

    type IntoIter = std::array::IntoIter<F, COEFFICIENTS>;

    fn into_iter(self) -> Self::IntoIter {
        self.coefficients.into_iter()
    }
}

impl<F: FieldElement, const COEFFICIENTS: usize> ops::Add
    for PolynomialRingElement<F, COEFFICIENTS>
{
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut result = PolynomialRingElement::<F, COEFFICIENTS>::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = self.coefficients[i] + other.coefficients[i];
        }
        result
    }
}
impl<F: FieldElement, const COEFFICIENTS: usize> ops::Sub
    for PolynomialRingElement<F, COEFFICIENTS>
{
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut result = PolynomialRingElement::<F, COEFFICIENTS>::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = self.coefficients[i] - other.coefficients[i];
        }
        result
    }
}
