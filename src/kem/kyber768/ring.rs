use std::ops::{self, Index, IndexMut};

use crate::kem::kyber768::{
    field_element::KyberFieldElement,
    parameters::COEFFICIENTS_IN_RING_ELEMENT,
};

use crate::kem::kyber768::utils::field::FieldElement;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KyberPolynomialRingElement {
    pub(crate) coefficients: [KyberFieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl KyberPolynomialRingElement {
    pub const ZERO: Self = Self {
        coefficients: [KyberFieldElement::ZERO; COEFFICIENTS_IN_RING_ELEMENT],
    };

    pub fn new(coefficients: [KyberFieldElement; COEFFICIENTS_IN_RING_ELEMENT]) -> Self {
        Self { coefficients }
    }

    pub fn coefficients(&self) -> &[KyberFieldElement; COEFFICIENTS_IN_RING_ELEMENT] {
        &self.coefficients
    }

    pub fn len(&self) -> usize {
        self.coefficients.len()
    }
}

impl Index<usize> for KyberPolynomialRingElement
{
    type Output = KyberFieldElement;

    fn index(&self, index: usize) -> &Self::Output {
        &self.coefficients[index]
    }
}
impl IndexMut<usize> for KyberPolynomialRingElement
{
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.coefficients[index]
    }
}

impl IntoIterator for KyberPolynomialRingElement
{
    type Item = KyberFieldElement;

    type IntoIter = std::array::IntoIter<KyberFieldElement, COEFFICIENTS_IN_RING_ELEMENT>;

    fn into_iter(self) -> Self::IntoIter {
        self.coefficients.into_iter()
    }
}

impl ops::Add for KyberPolynomialRingElement
{
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut result = KyberPolynomialRingElement::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = FieldElement::add(self.coefficients[i], other.coefficients[i]);
        }
        result
    }
}

impl ops::Sub for KyberPolynomialRingElement
{
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut result = KyberPolynomialRingElement::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = FieldElement::sub(self.coefficients[i], other.coefficients[i]);
        }
        result
    }
}
