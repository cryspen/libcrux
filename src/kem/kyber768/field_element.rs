use std::ops;

use crate::kem::kyber768::{parameters::FIELD_MODULUS, utils::field::FieldElement};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KyberFieldElement {
    pub value: u16,
}

impl KyberFieldElement {
    pub const MODULUS: u16 = FIELD_MODULUS;

    const BARRETT_SHIFT : u32 = 24; // 2 * ceil(log_2(FIELD_MODULUS))
    const BARRETT_MULTIPLIER : u32 = (1u32 << Self::BARRETT_SHIFT) / (Self::MODULUS as u32);

    pub fn barrett_reduce(value : u32) -> Self {
        let product : u64 = u64::from(value) * u64::from(Self::BARRETT_MULTIPLIER);
        let quotient : u32 = (product >> Self::BARRETT_SHIFT) as u32;

        let remainder = value - (quotient * u32::from(Self::MODULUS));
        let remainder : u16 = remainder as u16;

        let remainder_minus_modulus = remainder.wrapping_sub(Self::MODULUS);

        // TODO: Check if LLVM detects this and optimizes it away into a
        // conditional.
        let selector = 0u16.wrapping_sub((remainder_minus_modulus >> 15) & 1);

        Self {
            value: (selector & remainder) | (!selector & remainder_minus_modulus),
        }
    }
}

impl FieldElement for KyberFieldElement {
    const ZERO: Self = Self { value: 0 };

    fn new(number: u16) -> Self {
        Self::barrett_reduce(u32::from(number))
    }
}

impl From<u8> for KyberFieldElement {
    fn from(number: u8) -> Self {
        Self {
            value: u16::from(number)
        }
    }
}

impl From<KyberFieldElement> for u16 {
    fn from(fe: KyberFieldElement) -> Self {
        fe.value
    }
}

impl ops::Add for KyberFieldElement {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let sum: u16 = self.value + other.value;
        let difference: u16 = sum.wrapping_sub(Self::MODULUS);

        let mask = 0u16.wrapping_sub((difference >> 15) & 1);

        Self {
            value: (mask & sum) | (!mask & difference),
        }
    }
}
impl ops::Sub for KyberFieldElement {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let lhs = self.value;
        let rhs = Self::MODULUS - other.value;

        let sum: u16 = lhs + rhs;
        let difference: u16 = sum.wrapping_sub(Self::MODULUS);

        let mask = 0u16.wrapping_sub((difference >> 15) & 1);

        Self {
            value: (mask & sum) | (!mask & difference),
        }
    }
}

impl ops::Mul for KyberFieldElement {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let product: u32 = u32::from(self.value) * u32::from(other.value);

        Self::barrett_reduce(product)
    }
}

impl ops::Mul<u16> for KyberFieldElement {
    type Output = Self;

    fn mul(self, other: u16) -> Self {
        let product: u32 = u32::from(self.value) * u32::from(other);

        Self::barrett_reduce(product)
    }
}
