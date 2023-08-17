use std::ops::{self, Index, IndexMut};

use crate::kem::kyber768::parameters::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

pub(crate) type KyberFieldElement = i16;

const BARRETT_SHIFT: u32 = 24; // 2 * ceil(log_2(FIELD_MODULUS))
const BARRETT_MULTIPLIER: u64 = (1u64 << BARRETT_SHIFT) / (FIELD_MODULUS as u64);

pub(crate) fn barrett_reduce(value: i32) -> KyberFieldElement {
    let product: u64 = (value as u64) * BARRETT_MULTIPLIER;
    let quotient: u32 = (product >> BARRETT_SHIFT) as u32;

    // TODO: Justify in the comments (and subsequently in the proofs) that these
    // operations do not lead to overflow/underflow.
    let remainder = (value as u32) - (quotient * (FIELD_MODULUS as u32));
    let remainder: i16 = remainder as i16;

    let remainder_minus_modulus = remainder - FIELD_MODULUS;

    // TODO: Check if LLVM detects this and optimizes it away into a
    // conditional.
    let selector = remainder_minus_modulus >> 15;

    (selector & remainder) | (!selector & remainder_minus_modulus)
}

pub(crate) fn fe_add(lhs: KyberFieldElement, rhs: KyberFieldElement) -> KyberFieldElement {
    let sum: i16 = lhs + rhs;
    let difference: i16 = sum - FIELD_MODULUS;

    let mask = difference >> 15;

    (mask & sum) | (!mask & difference)
}

pub(crate) fn fe_sub(lhs: KyberFieldElement, rhs: KyberFieldElement) -> KyberFieldElement {
    let difference = lhs - rhs;
    let difference_plus_modulus: i16 = difference + FIELD_MODULUS;

    let mask = difference >> 15;

    (!mask & difference) | (mask & difference_plus_modulus)
}

pub(crate) fn fe_mul(lhs: KyberFieldElement, rhs: KyberFieldElement) -> KyberFieldElement {
    let product: i32 = i32::from(lhs) * i32::from(rhs);

    barrett_reduce(product)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KyberPolynomialRingElement {
    pub(crate) coefficients: [KyberFieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl KyberPolynomialRingElement {
    pub const ZERO: Self = Self {
        coefficients: [0i16; COEFFICIENTS_IN_RING_ELEMENT],
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

impl Index<usize> for KyberPolynomialRingElement {
    type Output = KyberFieldElement;

    fn index(&self, index: usize) -> &Self::Output {
        &self.coefficients[index]
    }
}
impl IndexMut<usize> for KyberPolynomialRingElement {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.coefficients[index]
    }
}

impl IntoIterator for KyberPolynomialRingElement {
    type Item = KyberFieldElement;

    type IntoIter = std::array::IntoIter<KyberFieldElement, COEFFICIENTS_IN_RING_ELEMENT>;

    fn into_iter(self) -> Self::IntoIter {
        self.coefficients.into_iter()
    }
}

impl ops::Add for KyberPolynomialRingElement {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut result = KyberPolynomialRingElement::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = fe_add(self.coefficients[i], other.coefficients[i]);
        }
        result
    }
}

impl ops::Sub for KyberPolynomialRingElement {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut result = KyberPolynomialRingElement::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = fe_sub(self.coefficients[i], other.coefficients[i]);
        }
        result
    }
}
