use std::ops::{self, Index, IndexMut};

use crate::kem::kyber768::parameters::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

pub(crate) type KyberFieldElement = i16;

const BARRETT_SHIFT: i32 = 26;
const BARRETT_R: i32 = 1i32 << BARRETT_SHIFT;
const BARRETT_MULTIPLIER: i32 = 20159; // floor((BARRETT_R / FIELD_MODULUS) + 0.5)

pub(crate) fn barrett_reduce(value: i16) -> KyberFieldElement {
    let quotient = (i32::from(value) * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    let quotient = (quotient >> BARRETT_SHIFT) as i16;

    value - (quotient * FIELD_MODULUS)
}

pub(crate) fn fe_mul(lhs: KyberFieldElement, rhs: KyberFieldElement) -> KyberFieldElement {
    // TODO: This will shortly be replaced by an implementation of
    // montgomery reduction.
    let product: i32 = i32::from(lhs) * i32::from(rhs);

    let reduced = (product % i32::from(FIELD_MODULUS)) as i16;

    if reduced > FIELD_MODULUS / 2 {
        reduced - FIELD_MODULUS
    } else if reduced < -FIELD_MODULUS / 2 {
        reduced + FIELD_MODULUS
    } else {
        reduced
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KyberPolynomialRingElement {
    pub(crate) coefficients: [KyberFieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl KyberPolynomialRingElement {
    pub const ZERO: Self = Self {
        coefficients: [0i16; COEFFICIENTS_IN_RING_ELEMENT],
    };
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
        for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
            result.coefficients[i] = self.coefficients[i] + other.coefficients[i];
        }
        result
    }
}

impl ops::Sub for KyberPolynomialRingElement {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut result = KyberPolynomialRingElement::ZERO;
        for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
            result.coefficients[i] = self.coefficients[i] - other.coefficients[i];
        }
        result
    }
}
