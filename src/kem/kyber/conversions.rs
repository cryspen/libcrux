use super::{arithmetic::KyberFieldElement, constants::FIELD_MODULUS};

#[inline(always)]
pub(super) fn into_padded_array<const LEN: usize>(slice: &[u8]) -> [u8; LEN] {
    debug_assert!(slice.len() <= LEN);
    let mut out = [0u8; LEN];
    out[0..slice.len()].copy_from_slice(slice);
    out
}

pub trait UpdatingArray {
    fn push(self, other: &[u8]) -> Self;
}

pub struct UpdatableArray<const LEN: usize> {
    value: [u8; LEN],
    pointer: usize,
}

impl<const LEN: usize> UpdatableArray<LEN> {
    #[inline(always)]
    pub fn new(value: [u8; LEN]) -> Self {
        Self { value, pointer: 0 }
    }

    #[inline(always)]
    pub fn array(self) -> [u8; LEN] {
        self.value
    }
}

impl<const LEN: usize> UpdatingArray for UpdatableArray<LEN> {
    #[inline(always)]
    fn push(mut self, other: &[u8]) -> Self {
        self.value[self.pointer..self.pointer + other.len()].copy_from_slice(other);
        self.pointer += other.len();
        self
    }
}

#[inline(always)]
pub(crate) fn to_unsigned_representative(fe: KyberFieldElement) -> u16 {
    (fe + ((fe >> 15) & FIELD_MODULUS)) as u16
}
