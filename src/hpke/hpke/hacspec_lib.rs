// === hacspec helper - remove
pub type Bytes = Vec<u8>;
use std::{
    num::ParseIntError,
    ops::{BitXor, Index, IndexMut},
};

pub(crate) fn bitxor(lhs: Vec<u8>, rhs: Vec<u8>) -> Vec<u8> {
    debug_assert_eq!(lhs.len(), rhs.len());
    let mut out = vec![0u8; lhs.len()];
    for i in 0..lhs.len() {
        out[i] = lhs[i] ^ rhs[i]
    }
    out
}
// === end hacspec helper - remove

pub trait HacspecVec {
    fn slice(&self, start_out: usize, len: usize) -> Self;
    fn into_slice(self, start_out: usize, len: usize) -> Self;
    fn concat(self, next: Self) -> Self;
    fn create(arg: usize) -> Self;
    fn update_slice(
        self,
        start_out: usize,
        v: impl AsRef<[u8]>,
        start_in: usize,
        len: usize,
    ) -> Self;
    fn from_hex(s: &str) -> Self;
    fn from_u16(x: u16) -> Self;
    fn from_u32(x: u32) -> Self;
    fn split(self, at: usize) -> (Self, Self)
    where
        Self: Sized;
}

impl HacspecVec for Vec<u8> {
    fn slice(&self, start_out: usize, len: usize) -> Self {
        self[start_out..start_out + len].to_vec()
    }
    fn into_slice(mut self, start_out: usize, len: usize) -> Self {
        self.drain(start_out..start_out + len).collect()
    }
    fn create(arg: usize) -> Self {
        vec![0u8; arg]
    }
    fn update_slice(
        mut self,
        start_out: usize,
        v: impl AsRef<[u8]>,
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
        let v = v.as_ref();
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
    fn from_hex(s: &str) -> Self {
        debug_assert!(s.len() % 2 == 0);
        let b: Result<Vec<u8>, ParseIntError> = (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
            .collect();
        b.expect("Error parsing hex string")
    }

    fn from_u16(x: u16) -> Self {
        x.to_be_bytes().to_vec()
    }

    fn from_u32(x: u32) -> Self {
        x.to_be_bytes().to_vec()
    }

    fn concat(mut self, mut next: Self) -> Self {
        self.append(&mut next);
        self
    }
    fn split(mut self, at: usize) -> (Self, Self) {
        let other = self.split_off(at);
        (self, other)
    }
}
