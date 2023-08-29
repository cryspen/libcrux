pub trait ArrayConversion<const LEN: usize> {
    fn as_array(&self) -> [u8; LEN];
    fn to_padded_array(&self) -> [u8; LEN];
}

impl<const LEN: usize> ArrayConversion<LEN> for &[u8] {
    fn as_array(&self) -> [u8; LEN] {
        self.to_vec().try_into().unwrap()
    }

    fn to_padded_array(&self) -> [u8; LEN] {
        assert!(self.len() <= LEN);
        let mut out = [0u8; LEN];
        out[0..self.len()].copy_from_slice(self);
        out
    }
}

pub trait ArrayPadding<const LEN: usize> {
    fn to_padded_array<const OLEN: usize>(&self) -> [u8; OLEN];
}

impl<const LEN: usize> ArrayPadding<LEN> for &[u8; LEN] {
    fn to_padded_array<const OLEN: usize>(&self) -> [u8; OLEN] {
        assert!(self.len() <= OLEN);
        let mut out = [0u8; OLEN];
        out[0..self.len()].copy_from_slice(*self);
        out
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

    pub fn array(self) -> [u8; LEN] {
        self.value
    }
}

impl<const LEN: usize> UpdatingArray for UpdatableArray<LEN> {
    fn push(mut self, other: &[u8]) -> Self {
        self.value[self.pointer..self.pointer + other.len()].copy_from_slice(other);
        self.pointer += other.len();
        self
    }
}
