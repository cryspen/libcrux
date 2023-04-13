// === hacspec helper - remove
#[derive(Clone)]
pub struct Bytes(pub(crate) Vec<u8>);
pub(crate) type U16 = u16;
pub(crate) fn U16(v: u16) -> U16 {
    v
}
pub(crate) type U32 = u32;
pub(crate) fn U32(v: u32) -> U32 {
    v
}
pub(crate) fn Byte(v: u8) -> u8 {
    v
}
macro_rules! create_bytes {
    ($( $b:expr ),+) => {
        Bytes(vec![
            $(
                $b
            ),+
        ])
    };
}
use std::{
    num::ParseIntError,
    ops::{BitXor, Index, IndexMut},
};

pub(crate) use create_bytes;
impl Bytes {
    pub(crate) fn concat_owned(mut self, mut next: Bytes) -> Bytes {
        self.0.append(&mut next.0);
        self
    }
    pub(crate) fn concat_slice(mut self, next: impl AsRef<[u8]>) -> Bytes {
        self.0.extend_from_slice(next.as_ref());
        self
    }
    pub(crate) fn concat(mut self, next: &Bytes) -> Bytes {
        self.0.extend_from_slice(&next.0);
        self
    }
    pub(crate) fn into_slice(mut self, start_out: usize, len: usize) -> Bytes {
        self.0 = self.0.drain(start_out..start_out + len).collect();
        self
    }
    pub(crate) fn new(arg: usize) -> Self {
        Bytes(vec![0u8; arg])
    }
    pub(crate) fn slice(&self, start_out: usize, len: usize) -> Self {
        Self(self.0[start_out..start_out + len].to_vec())
    }
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }
    pub(crate) fn split_off(mut self, at: usize) -> (Self, Self) {
        let other = Self(self.0.split_off(at));
        (self, other)
    }
    pub(crate) fn update_slice(
        mut self,
        start_out: usize,
        v: &Bytes,
        start_in: usize,
        len: usize,
    ) -> Self {
        debug_assert!(
            self.len() >= start_out + len,
            "{} < {} + {}",
            self.len(),
            start_out,
            len
        );
        debug_assert!(
            v.len() >= start_in + len,
            "{} < {} + {}",
            v.len(),
            start_in,
            len
        );
        for i in 0..len {
            self[start_out + i] = v[start_in + i].clone();
        }
        self
    }
    pub fn from_hex(s: &str) -> Self {
        debug_assert!(s.len() % 2 == 0);
        let b: Result<Vec<u8>, ParseIntError> = (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
            .collect();
        Self(b.expect("Error parsing hex string"))
    }
}

impl AsRef<[u8]> for Bytes {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Index<usize> for Bytes {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}
impl IndexMut<usize> for Bytes {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(value: Vec<u8>) -> Self {
        Self(value)
    }
}
impl From<u16> for Bytes {
    fn from(value: u16) -> Self {
        Bytes(value.to_be_bytes().to_vec())
    }
}
impl From<u32> for Bytes {
    fn from(value: u32) -> Self {
        Bytes(value.to_be_bytes().to_vec())
    }
}

impl BitXor for Bytes {
    type Output = Bytes;
    fn bitxor(self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.len(), rhs.len());
        let mut out = Self::new(self.len());
        for i in 0..self.len() {
            out[i] = self[i] ^ rhs[i]
        }
        out
    }
}
// === end hacspec helper - remove
