use std::ops::{self, Index, IndexMut};

use super::constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

pub(crate) type KyberFieldElement = i32;

const BARRETT_SHIFT: i32 = 26;
const BARRETT_R: i32 = 1i32 << BARRETT_SHIFT;
const BARRETT_MULTIPLIER: i32 = 20159; // floor((BARRETT_R / FIELD_MODULUS) + 0.5)

pub(crate) fn barrett_reduce(value: KyberFieldElement) -> KyberFieldElement {
    debug_assert!(value > -BARRETT_R / 2);
    debug_assert!(value < BARRETT_R / 2);

    let quotient = ((value * BARRETT_MULTIPLIER) + (BARRETT_R >> 1)) >> BARRETT_SHIFT;

    let reduced = value - (quotient * FIELD_MODULUS);

    debug_assert!(reduced > -FIELD_MODULUS);
    debug_assert!(reduced < FIELD_MODULUS);

    reduced
}

const MONTGOMERY_SHIFT: i32 = 16;
const MONTGOMERY_R: i32 = 1i32 << MONTGOMERY_SHIFT;
const INVERSE_OF_MODULUS_MOD_R: i32 = -3327; // FIELD_MODULUS^{-1} mod MONTGOMERY_R

pub(crate) fn montgomery_reduce(value: KyberFieldElement) -> KyberFieldElement {
    debug_assert!(value > -FIELD_MODULUS * (MONTGOMERY_R / 2));
    debug_assert!(value < FIELD_MODULUS * (MONTGOMERY_R / 2));

    let t = (value & (MONTGOMERY_R - 1)) * INVERSE_OF_MODULUS_MOD_R;
    let t = (t & (MONTGOMERY_R - 1)) as i16;

    let reduced =
        (value >> MONTGOMERY_SHIFT) - ((i32::from(t) * FIELD_MODULUS) >> MONTGOMERY_SHIFT);

    debug_assert!(reduced > -FIELD_MODULUS);
    debug_assert!(reduced < FIELD_MODULUS);

    reduced
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KyberPolynomialRingElement {
    pub(crate) coefficients: [KyberFieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl KyberPolynomialRingElement {
    pub const ZERO: Self = Self {
        coefficients: [0i32; 256], // FIXME: hax issue, this is COEFFICIENTS_IN_RING_ELEMENT
    };
}

// Adding this to a module to ignore it for extraction.
mod mutable_operations {
    use super::*;

    impl IndexMut<usize> for KyberPolynomialRingElement {
        fn index_mut(&mut self, index: usize) -> &mut Self::Output {
            &mut self.coefficients[index]
        }
    }
}

impl Index<usize> for KyberPolynomialRingElement {
    type Output = KyberFieldElement;

    fn index(&self, index: usize) -> &Self::Output {
        &self.coefficients[index]
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
