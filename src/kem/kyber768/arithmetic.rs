use std::ops::{self, Index, IndexMut};

use crate::kem::kyber768::parameters::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KyberFieldElement {
    pub value: i16,
}

impl KyberFieldElement {
    pub const ZERO: Self = Self { value: 0 };

    pub const MODULUS: i16 = FIELD_MODULUS as i16;

    const BARRETT_SHIFT: u32 = 24; // 2 * ceil(log_2(FIELD_MODULUS))
    const BARRETT_MULTIPLIER: u32 = (1u32 << Self::BARRETT_SHIFT) / (Self::MODULUS as u32);

    pub fn barrett_reduce(value: i32) -> Self {
        let product: u64 = (value as u64) * u64::from(Self::BARRETT_MULTIPLIER);
        let quotient: u32 = (product >> Self::BARRETT_SHIFT) as u32;

        let remainder = (value as u32) - (quotient * (Self::MODULUS as u32));
        let remainder: i16 = remainder as i16;

        let remainder_minus_modulus = remainder - Self::MODULUS;

        // TODO: Check if LLVM detects this and optimizes it away into a
        // conditional.
        let selector = remainder_minus_modulus >> 15;

        Self {
            value: (selector & remainder) | (!selector & remainder_minus_modulus),
        }
    }

    pub fn add(self, other: Self) -> Self {
        let sum: i16 = self.value + other.value;
        let difference: i16 = sum - Self::MODULUS;

        let mask = difference >> 15;

        Self {
            value: (mask & sum) | (!mask & difference),
        }
    }

    pub fn sub(self, other: Self) -> Self {
        let difference = self.value - other.value;
        let difference_plus_modulus: i16 = difference + Self::MODULUS;

        let mask = difference >> 15;

        Self {
            value: (!mask & difference) | (mask & difference_plus_modulus),
        }
    }

    pub fn mul(self, other: Self) -> Self {
        let product: i32 = i32::from(self.value) * i32::from(other.value);

        Self::barrett_reduce(product)
    }

    pub fn mul_by_u16(self, other: u16) -> Self {
        let product: i32 = i32::from(self.value) * i32::from(other);

        Self::barrett_reduce(product)
    }
}

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
            result.coefficients[i] = KyberFieldElement::add(self.coefficients[i], other.coefficients[i]);
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
            result.coefficients[i] = KyberFieldElement::sub(self.coefficients[i], other.coefficients[i]);
        }
        result
    }
}
