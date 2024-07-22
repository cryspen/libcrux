//! A portable SHA3 implementation using the generic implementation.

use crate::traits::internal::{self, *};

/// A portable buffer. A simple wrapper around a byte slice.
#[derive(Clone, Copy)]
pub(crate) struct Buf<'a> {
    buf: &'a [u8],
}

impl<'a> Buffer for Buf<'a> {
    fn len(&self) -> usize {
        self.buf.len()
    }

    fn slice(&self, start: usize, len: usize) -> Self {
        Self {
            buf: &self.buf[start..start + len],
        }
    }
}

impl<'a> From<&'a [u8]> for Buf<'a> {
    fn from(buf: &'a [u8]) -> Self {
        Self { buf }
    }
}

/// A portable block. A simple wrapper around a `[u8; 200]`.
#[derive(Clone, Copy)]
pub(crate) struct FullBuf {
    buf: [u8; 200],

    /// The length of the original buffer.
    eob: usize,
}

impl<'a> internal::Block<Buf<'a>> for FullBuf {
    fn init(b: Buf<'a>) -> Self {
        let mut buf = [0u8; 200];
        let eob = b.len();
        if eob > 0 {
            buf[0..b.len()].copy_from_slice(&b.buf);
        }
        Self { buf, eob }
    }

    fn set_constants<const DELIM: u8, const EOB: usize>(&mut self) {
        self.buf[self.eob] = DELIM;
        self.buf[EOB - 1] |= 0x80;
    }
}

#[inline(always)]
fn rotate_left<const LEFT: i32, const RIGHT: i32>(x: u64) -> u64 {
    debug_assert!(LEFT + RIGHT == 64);
    (x << LEFT) | (x >> RIGHT)
}

#[inline(always)]
fn _veor5q_u64(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {
    let ab = a ^ b;
    let cd = c ^ d;
    let abcd = ab ^ cd;
    abcd ^ e
}

#[inline(always)]
fn _vrax1q_u64(a: u64, b: u64) -> u64 {
    a ^ rotate_left::<1, 63>(b)
}

#[inline(always)]
fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(a: u64, b: u64) -> u64 {
    let ab = a ^ b;
    rotate_left::<LEFT, RIGHT>(ab)
}

#[inline(always)]
fn _vbcaxq_u64(a: u64, b: u64, c: u64) -> u64 {
    a ^ (b & !c)
}

#[inline(always)]
fn _veorq_n_u64(a: u64, c: u64) -> u64 {
    a ^ c
}

#[inline(always)]
pub(crate) fn load_block<'a, const BLOCK_SIZE: usize>(state: &mut [[u64; 5]; 5], blocks: Buf<'a>) {
    // FIXME: check that `blocks` if big enough if we want to keep this function
    debug_assert!(BLOCK_SIZE <= blocks.buf.len() && BLOCK_SIZE % 8 == 0);

    for i in 0..BLOCK_SIZE / 8 {
        state[i / 5][i % 5] ^= u64::from_le_bytes(blocks.buf[8 * i..8 * i + 8].try_into().unwrap());
    }
}

#[inline(always)]
pub(crate) fn load_block_full<const RATE: usize>(s: &mut [[u64; 5]; 5], blocks: FullBuf) {
    load_block::<RATE>(s, Buf { buf: &blocks.buf });
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(s: &[[u64; 5]; 5], out: [&mut [u8]; 1]) {
    for i in 0..RATE / 8 {
        out[0][8 * i..8 * i + 8].copy_from_slice(&s[i / 5][i % 5].to_le_bytes());
    }
}

#[inline(always)]
pub(crate) fn store_block_full<const RATE: usize>(s: &[[u64; 5]; 5]) -> [[u8; 200]; 1] {
    let mut out = [0u8; 200];
    store_block::<RATE>(s, [&mut out]);
    [out]
}

#[inline(always)]
fn slice_1(a: [&[u8]; 1], start: usize, len: usize) -> [&[u8]; 1] {
    [&a[0][start..start + len]]
}

#[inline(always)]
fn split_at_mut_1(out: [&mut [u8]; 1], mid: usize) -> ([&mut [u8]; 1], [&mut [u8]; 1]) {
    let (out00, out01) = out[0].split_at_mut(mid);
    ([out00], [out01])
}

impl<'a> KeccakItem<Buf<'a>, FullBuf, 1> for u64 {
    #[inline(always)]
    fn zero() -> Self {
        0
    }
    #[inline(always)]
    fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
        _veor5q_u64(a, b, c, d, e)
    }
    #[inline(always)]
    fn rotate_left1_and_xor(a: Self, b: Self) -> Self {
        _vrax1q_u64(a, b)
    }
    #[inline(always)]
    fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self {
        _vxarq_u64::<LEFT, RIGHT>(a, b)
    }
    #[inline(always)]
    fn and_not_xor(a: Self, b: Self, c: Self) -> Self {
        _vbcaxq_u64(a, b, c)
    }
    #[inline(always)]
    fn xor_constant(a: Self, c: u64) -> Self {
        _veorq_n_u64(a, c)
    }
    #[inline(always)]
    fn xor(a: Self, b: Self) -> Self {
        a ^ b
    }
    #[inline(always)]
    fn load_block<const BLOCKSIZE: usize>(state: &mut [[Self; 5]; 5], buf: Buf) {
        load_block::<BLOCKSIZE>(state, buf)
    }
    #[inline(always)]
    fn store_block<const BLOCKSIZE: usize>(a: &[[Self; 5]; 5], b: [&mut [u8]; 1]) {
        store_block::<BLOCKSIZE>(a, b)
    }
    #[inline(always)]
    fn load_block_full<const BLOCKSIZE: usize>(state: &mut [[Self; 5]; 5], block: FullBuf) {
        load_block_full::<BLOCKSIZE>(state, block)
    }
    #[inline(always)]
    fn store_block_full<const BLOCKSIZE: usize>(a: &[[Self; 5]; 5]) -> [[u8; 200]; 1] {
        store_block_full::<BLOCKSIZE>(a)
    }
    #[inline(always)]
    fn slice_n(a: [&[u8]; 1], start: usize, len: usize) -> [&[u8]; 1] {
        slice_1(a, start, len)
    }
    #[inline(always)]
    fn split_at_mut_n(a: [&mut [u8]; 1], mid: usize) -> ([&mut [u8]; 1], [&mut [u8]; 1]) {
        split_at_mut_1(a, mid)
    }
}
