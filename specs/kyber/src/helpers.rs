pub(crate) mod bit_vector;
pub(crate) mod field;
pub(crate) mod ring;

pub trait PanickingIntegerCasts {
    fn as_u8(self) -> u8;
    fn as_u16(self) -> u16;
    fn as_u32(self) -> u32;
}

impl PanickingIntegerCasts for usize {
    fn as_u8(self) -> u8 {
        self.try_into().unwrap()
    }

    fn as_u16(self) -> u16 {
        self.try_into().unwrap()
    }

    fn as_u32(self) -> u32 {
        self.try_into().unwrap()
    }
}

pub trait PanickingArrayConversion {
    fn as_array<const LEN: usize>(&self) -> [u8; LEN];
    fn into_array<const LEN: usize>(self) -> [u8; LEN];
}

impl PanickingArrayConversion for Vec<u8> {
    fn as_array<const LEN: usize>(&self) -> [u8; LEN] {
        self.clone().try_into().unwrap()
    }

    fn into_array<const LEN: usize>(self) -> [u8; LEN] {
        self.try_into().unwrap()
    }
}

pub trait ArrayUpdate {
    fn update(self, start: usize, other: &[u8]) -> Self;
}

impl<const LEN: usize> ArrayUpdate for [u8; LEN] {
    fn update(mut self, start: usize, other: &[u8]) -> Self {
        self[start..start + other.len()].copy_from_slice(other);
        self
    }
}

pub trait UpdatingArray {
    fn push(self, other: &[u8]) -> Self;
}

pub struct UpdatableArray<const LEN: usize> {
    value: [u8; LEN],
    pointer: usize,
}

impl<const LEN: usize> UpdatableArray<LEN> {
    pub fn new(value: [u8; LEN]) -> Self {
        Self { value, pointer: 0 }
    }
}

impl<const LEN: usize> UpdatingArray for UpdatableArray<LEN> {
    fn push(mut self, other: &[u8]) -> Self {
        self.value[self.pointer..self.pointer + other.len()].copy_from_slice(other);
        self.pointer += other.len();
        self
    }
}

impl<const LEN: usize> From<[u8; LEN]> for UpdatableArray<LEN> {
    fn from(value: [u8; LEN]) -> Self {
        Self { value, pointer: 0 }
    }
}

impl<const LEN: usize> From<UpdatableArray<LEN>> for [u8; LEN] {
    fn from(value: UpdatableArray<LEN>) -> Self {
        value.value
    }
}

#[cfg(test)]
pub(crate) mod testing {
    use crate::parameters::{self, KyberFieldElement, KyberPolynomialRingElement};

    use proptest::collection::vec;
    use proptest::prelude::*;

    prop_compose! {
        fn arb_field_element(bit_size : usize) (
            representative in 0u16..parameters::FIELD_MODULUS) -> KyberFieldElement {
                (representative & ((1 << bit_size) - 1)).into()
        }
    }

    prop_compose! {
        pub(crate) fn arb_ring_element(bits_per_coefficient : usize) (arb_ring_coefficients in vec(arb_field_element(bits_per_coefficient), parameters::COEFFICIENTS_IN_RING_ELEMENT)) -> KyberPolynomialRingElement {
                KyberPolynomialRingElement {
                    coefficients: arb_ring_coefficients.try_into().unwrap(),
            }
        }
    }
}
