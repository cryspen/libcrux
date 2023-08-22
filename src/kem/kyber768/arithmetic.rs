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

const MONTGOMERY_SHIFT: i64 = 16;
const MONTGOMERY_R: i64 = 1i64 << MONTGOMERY_SHIFT;
const INVERSE_OF_MODULUS_MOD_R: i64 = -3327; // FIELD_MODULUS^{-1} mod MONTGOMERY_R

pub(crate) fn montgomery_reduce(value: i32) -> KyberFieldElement {
    let t: i64 = i64::from(value) * INVERSE_OF_MODULUS_MOD_R;
    let t: i32 = (t & (MONTGOMERY_R - 1)) as i32;

    let t = value - (t * i32::from(FIELD_MODULUS));

    (t >> MONTGOMERY_SHIFT) as i16
}

// Given a |value|, return |value|*R mod q. Notice that montgomery_reduce
// returns a value aR^{-1} mod q, and so montgomery_reduce(|value| * R^2)
// returns |value| * R^2 & R^{-1} mod q  = |value| * R mod q.
pub(crate) fn to_montgomery_domain(value: i32) -> KyberFieldElement {
    // R^2 mod q = (2^16)^2 mod 3329 = 1353
    montgomery_reduce(1353 * value)
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
