//! A portable SHA3 implementation using the generic implementation.

use crate::traits::internal::*;

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
pub(crate) fn load_block<const RATE: usize>(s: &mut [[u64; 5]; 5], blocks: &[u8]) {
    debug_assert!(RATE <= blocks.len() && RATE % 8 == 0);
    for i in 0..RATE / 8 {
        s[i / 5][i % 5] ^= u64::from_le_bytes(blocks[8 * i..8 * i + 8].try_into().unwrap());
    }
}

#[inline(always)]
pub(crate) fn load_block_full<const RATE: usize>(s: &mut [[u64; 5]; 5], blocks: [u8; 200]) {
    load_block::<RATE>(s, &blocks);
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(s: &[[u64; 5]; 5], out: &mut [u8]) {
    for i in 0..RATE / 8 {
        out[8 * i..8 * i + 8].copy_from_slice(&s[i / 5][i % 5].to_le_bytes());
    }
}

#[inline(always)]
pub(crate) fn store_block_full<const RATE: usize>(s: &[[u64; 5]; 5]) -> [u8; 200] {
    let mut out = [0u8; 200];
    store_block::<RATE>(s, &mut out);
    out
}

#[inline(always)]
fn slice_1(a: &[u8], start: usize, len: usize) -> &[u8] {
    &a[start..start + len]
}

#[inline(always)]
fn split_at_mut_1(out: &mut [u8], mid: usize) -> (&mut [u8], &mut [u8]) {
    out.split_at_mut(mid)
}

impl KeccakItem<1> for u64 {
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
    fn load_block<const RATE: usize>(a: &mut [[Self; 5]; 5], b: [&[u8]; 1]) {
        load_block::<RATE>(a, b[0])
    }
    #[inline(always)]
    fn store_block<const RATE: usize>(a: &[[Self; 5]; 5], b: [&mut [u8]; 1]) {
        store_block::<RATE>(a, b[0])
    }
    #[inline(always)]
    fn load_block_full<const RATE: usize>(a: &mut [[Self; 5]; 5], b: [[u8; 200]; 1]) {
        load_block_full::<RATE>(a, b[0])
    }
    #[inline(always)]
    fn store_block_full<const RATE: usize>(a: &[[Self; 5]; 5]) -> [[u8; 200]; 1] {
        [store_block_full::<RATE>(a)]
    }
    #[inline(always)]
    fn slice_n(a: [&[u8]; 1], start: usize, len: usize) -> [&[u8]; 1] {
        [slice_1(a[0], start, len)]
    }
    #[inline(always)]
    fn split_at_mut_n(a: [&mut [u8]; 1], mid: usize) -> ([&mut [u8]; 1], [&mut [u8]; 1]) {
        let (x, y) = split_at_mut_1(a[0], mid);
        ([x], [y])
    }

    /// `out` has the exact size we want here. It must be less than or equal to `RATE`.
    #[inline(always)]
    fn store<const RATE: usize>(state: &[[Self; 5]; 5], out: [&mut [u8]; 1]) {
        debug_assert!(out.len() <= RATE / 8, "{} > {}", out.len(), RATE);

        let num_full_blocks = out[0].len() / 8;
        let last_block_len = out[0].len() % 8;

        for i in 0..num_full_blocks {
            out[0][i * 8..i * 8 + 8].copy_from_slice(&state[i / 5][i % 5].to_le_bytes());
        }
        if last_block_len != 0 {
            out[0][num_full_blocks * 8..num_full_blocks * 8 + last_block_len].copy_from_slice(
                &state[num_full_blocks / 5][num_full_blocks % 5].to_le_bytes()[0..last_block_len],
            );
        }
    }
}
