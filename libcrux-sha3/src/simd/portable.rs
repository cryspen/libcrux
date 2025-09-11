//! A portable SHA3 implementation using the generic implementation.

use hax_lib::int::*;

use crate::{generic_keccak::KeccakState, traits::*};

#[inline(always)]
fn rotate_left<const LEFT: i32, const RIGHT: i32>(x: u64) -> u64 {
    debug_assert!(LEFT + RIGHT == 64);
    u64::rotate_left(x, LEFT as u32)
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
#[hax_lib::requires(
    RATE < 192 &&
    RATE % 8 == 0 &&
    start.to_int() + RATE.to_int() <= blocks.len().to_int()
)]
pub(crate) fn load_block<const RATE: usize>(state: &mut [u64; 25], blocks: &[u8], start: usize) {
    debug_assert!(start + RATE <= blocks.len());
    debug_assert!(RATE % 8 == 0);

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
            *get_ij(state, i / 5, i % 5) ^ state_flat[i],
        );
    }
}

#[inline(always)]
#[hax_lib::requires(
    RATE < 192 &&
    RATE % 8 == 0 &&
    len < RATE &&
    len < blocks.len() &&
    start <= blocks.len() &&
    start <= blocks.len() - len &&
    start + len <= blocks.len()
)]
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
#[hax_lib::requires(
    len < 192 &&
    len <= out.len() &&
    start <= out.len() &&
    start <= out.len() - len &&
    start + len <= out.len()
)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn store_block<const RATE: usize>(
    s: &[u64; 25],
    out: &mut [u8],
    start: usize,
    len: usize,
) {
    let octets = len / 8;

    #[cfg(hax)]
    let out_len = out.len(); // ghost variable

    for i in 0..octets {
        hax_lib::loop_invariant!(|i: usize| out.len() == out_len);
        hax_lib::fstar!("assert (v $i < v $octets)");
        hax_lib::fstar!("assert (v $i + 1 <= v $octets)");
        hax_lib::fstar!("assert (8 * (v $i + 1) <= 8 * v $octets)");
        hax_lib::fstar!("assert (8 * v $octets <= v $len)");
        hax_lib::fstar!("assert (v $start + 8 * (v $i + 1) <= v $start + v $len)");
        hax_lib::fstar!("assert (v $start + v $len <= Seq.length $out)");
        let value = get_ij(s, i / 5, i % 5);
        let bytes = value.to_le_bytes();
        let out_pos = start + 8 * i;
        hax_lib::fstar!("assert (v $out_pos + 8 <= Seq.length $out)");
        hax_lib::fstar!("assert (v $start + 8 * v $i + 8 <= v $start + v $len)");
        out[out_pos..out_pos + 8].copy_from_slice(&bytes);
    }

    let remaining = len % 8;
    if remaining > 0 {
        let value = get_ij(s, octets / 5, octets % 5);
        let bytes = value.to_le_bytes();
        let out_pos = start + len - remaining;
        hax_lib::fstar!("assert (v $start + v $len <= Seq.length $out)");
        hax_lib::fstar!("assert (v $out_pos + v $remaining == v $start + v $len)");
        hax_lib::fstar!("assert (v $out_pos + v $remaining <= Seq.length $out)");
        out[out_pos..out_pos + remaining].copy_from_slice(&bytes[..remaining]);
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
}

#[hax_lib::attributes]
impl Absorb<1> for KeccakState<1, u64> {
    #[hax_lib::requires(
        RATE < 192 &&
        RATE % 8 == 0 &&
        RATE <= input[0].len() &&
        start <= input[0].len() &&
        start <= input[0].len() - RATE &&
        start + RATE <= input[0].len()
    )]
    fn load_block<const RATE: usize>(&mut self, input: &[&[u8]; 1], start: usize) {
        load_block::<RATE>(&mut self.st, input[0], start);
    }

    #[hax_lib::requires(
        RATE < 192 &&
        RATE % 8 == 0 &&
        len < RATE &&
        len < input[0].len() &&
        start <= input[0].len() &&
        start <= input[0].len() - len &&
        start + len <= input[0].len()
    )]
    fn load_last<const RATE: usize, const DELIMITER: u8>(
        &mut self,
        input: &[&[u8]; 1],
        start: usize,
        len: usize,
    ) {
        load_last::<RATE, DELIMITER>(&mut self.st, input[0], start, len);
    }
}

#[hax_lib::attributes]
impl Squeeze<u64> for KeccakState<1, u64> {
    #[hax_lib::requires(
        len < 192 &&
        len <= out.len() &&
        start <= out.len() &&
        start <= out.len() - len &&
        start + len <= out.len()
    )]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    fn squeeze<const RATE: usize>(&self, out: &mut [u8], start: usize, len: usize) {
        store_block::<RATE>(&self.st, out, start, len);
    }
}
