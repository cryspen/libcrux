//! A portable SHA3 implementation using the generic implementation.

use crate::traits::{internal::*, *};

#[inline(always)]
fn rotate_left<const LEFT: i32, const RIGHT: i32>(x: u64) -> u64 {
    debug_assert!(LEFT + RIGHT == 64);
    x.rotate_left(LEFT as u32)
}

#[inline(always)]
fn _veor5q_u64(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {
    a ^ b ^ c ^ d ^ e
}

#[inline(always)]
fn _vrax1q_u64(a: u64, b: u64) -> u64 {
    a ^ rotate_left::<1, 63>(b)
}

#[inline(always)]
fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(a: u64, b: u64) -> u64 {
    rotate_left::<LEFT, RIGHT>(a ^ b)
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
pub(crate) fn load_block<const RATE: usize>(state: &mut [u64; 25], blocks: &[u8], start: usize) {
    debug_assert!(start + RATE <= blocks.len() && RATE % 8 == 0);

    // First load the block, then xor it with the state
    // Note: combining the two loops below reduces performance for large inputs,
    //       so we knowingly use two loops: one for loading, one for xor
    let mut state_flat = [0u64; 25];

    #[allow(clippy::needless_range_loop)]
    for i in 0..RATE / 8 {
        let offset = start + 8 * i;
        state_flat[i] = u64::from_le_bytes(blocks[offset..offset + 8].try_into().unwrap());
    }

    #[allow(clippy::needless_range_loop)]
    for i in 0..RATE / 8 {
        set_ij(
            state,
            i / 5,
            i % 5,
            get_ij(state, i / 5, i % 5) ^ state_flat[i],
        );
    }
}

#[inline(always)]
pub(crate) fn load_last<const RATE: usize, const DELIMITER: u8>(
    state: &mut [u64; 25],
    blocks: &[u8],
    start: usize,
    len: usize,
) {
    debug_assert!(start + len <= blocks.len());

    let mut buffer = [0u8; RATE];
    buffer[0..len].copy_from_slice(&blocks[start..start + len]);
    buffer[len] = DELIMITER;
    buffer[RATE - 1] |= 0x80;

    load_block::<RATE>(state, &buffer, 0);
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(
    s: &[u64; 25],
    out: &mut [u8],
    start: usize,
    len: usize,
) {
    let octets = len / 8;
    for i in 0..octets {
        out[start + 8 * i..start + 8 * i + 8]
            .copy_from_slice(&get_ij(s, i / 5, i % 5).to_le_bytes());
    }

    let remaining = len % 8;
    if remaining > 0 {
        out[start + len - remaining..start + len]
            .copy_from_slice(&get_ij(s, octets / 5, octets % 5).to_le_bytes()[0..remaining]);
    }
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
    fn load_block<const RATE: usize>(state: &mut [Self; 25], blocks: &[&[u8]; 1], start: usize) {
        load_block::<RATE>(state, blocks[0], start)
    }

    #[inline(always)]
    fn load_last<const RATE: usize, const DELIMITER: u8>(
        state: &mut [Self; 25],
        blocks: &[&[u8]; 1],
        start: usize,
        len: usize,
    ) {
        load_last::<RATE, DELIMITER>(state, blocks[0], start, len)
    }

    #[inline(always)]
    fn store_block<const RATE: usize>(
        state: &[Self; 25],
        out: &mut [&mut [u8]; 1],
        start: usize,
        len: usize,
    ) {
        store_block::<RATE>(state, out[0], start, len)
    }
}
