use libcrux_intrinsics::arm64::*;

use crate::traits::internal::KeccakItem;

#[allow(non_camel_case_types)]
pub type uint64x2_t = _uint64x2_t;

// This file optimizes for the stable Rust Neon Intrinsics
// If we want to use the unstable neon-sha3 instructions, we could use:
// veor3q_u64, vrax1q_u64, vxarq_u64, and vbcaxq_u64
// These instructions might speed up our code even more.

#[inline(always)]
fn rotate_left<const LEFT: i32, const RIGHT: i32>(x: uint64x2_t) -> uint64x2_t {
    debug_assert!(LEFT + RIGHT == 64);
    // The following looks faster but is actually significantly slower
    //unsafe { vsriq_n_u64::<RIGHT>(vshlq_n_u64::<LEFT>(x), x) }
    _veorq_u64(_vshlq_n_u64::<LEFT>(x), _vshrq_n_u64::<RIGHT>(x))
}

#[inline(always)]
fn _veor5q_u64(
    a: uint64x2_t,
    b: uint64x2_t,
    c: uint64x2_t,
    d: uint64x2_t,
    e: uint64x2_t,
) -> uint64x2_t {
    let ab = _veorq_u64(a, b);
    let cd = _veorq_u64(c, d);
    let abcd = _veorq_u64(ab, cd);
    _veorq_u64(abcd, e)
    // Needs nightly+neon-sha3
    //unsafe {veor3q_u64(veor3q_u64(a,b,c),d,e)}
}

#[inline(always)]
fn _vrax1q_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    _veorq_u64(a, rotate_left::<1, 63>(b))
    // Needs nightly+neon-sha3
    //unsafe { vrax1q_u64(a, b) }
}

#[inline(always)]
fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    let ab = _veorq_u64(a, b);
    rotate_left::<LEFT, RIGHT>(ab)
    // Needs nightly+neon-sha3
    // unsafe { vxarq_u64::<RIGHT>(a,b) }
}

#[inline(always)]
fn _vbcaxq_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
    _veorq_u64(a, _vbicq_u64(b, c))
    // Needs nightly+neon-sha3
    // unsafe{ vbcaxq_u64(a, b, c) }
}

#[inline(always)]
fn _veorq_n_u64(a: uint64x2_t, c: u64) -> uint64x2_t {
    let c = _vdupq_n_u64(c);
    _veorq_u64(a, c)
}

#[inline(always)]
pub(crate) fn load_block<const RATE: usize>(s: &mut [[uint64x2_t; 5]; 5], blocks: [&[u8]; 2]) {
    debug_assert!(RATE <= blocks[0].len() && RATE % 8 == 0);
    for i in 0..RATE / 16 {
        let v0 = _vld1q_bytes_u64(&blocks[0][16 * i..16 * (i + 1)]);
        let v1 = _vld1q_bytes_u64(&blocks[1][16 * i..16 * (i + 1)]);
        s[(2 * i) / 5][(2 * i) % 5] = _veorq_u64(s[(2 * i) / 5][(2 * i) % 5], _vtrn1q_u64(v0, v1));
        s[(2 * i + 1) / 5][(2 * i + 1) % 5] =
            _veorq_u64(s[(2 * i + 1) / 5][(2 * i + 1) % 5], _vtrn2q_u64(v0, v1));
    }
    if RATE % 16 != 0 {
        let i = (RATE / 8 - 1) / 5;
        let j = (RATE / 8 - 1) % 5;
        let mut u = [0u64; 2];
        u[0] = u64::from_le_bytes(blocks[0][RATE - 8..RATE].try_into().unwrap());
        u[1] = u64::from_le_bytes(blocks[1][RATE - 8..RATE].try_into().unwrap());
        let uvec = _vld1q_u64(&u);
        s[i][j] = _veorq_u64(s[i][j], uvec);
    }
}

#[inline(always)]
pub(crate) fn load_block_full<const RATE: usize>(
    s: &mut [[uint64x2_t; 5]; 5],
    blocks: [[u8; 200]; 2],
) {
    load_block::<RATE>(s, [&blocks[0] as &[u8], &blocks[1] as &[u8]]);
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(s: &[[uint64x2_t; 5]; 5], out: [&mut [u8]; 2]) {
    for i in 0..RATE / 16 {
        let v0 = _vtrn1q_u64(
            s[(2 * i) / 5][(2 * i) % 5],
            s[(2 * i + 1) / 5][(2 * i + 1) % 5],
        );
        let v1 = _vtrn2q_u64(
            s[(2 * i) / 5][(2 * i) % 5],
            s[(2 * i + 1) / 5][(2 * i + 1) % 5],
        );
        _vst1q_bytes_u64(&mut out[0][16 * i..16 * (i + 1)], v0);
        _vst1q_bytes_u64(&mut out[1][16 * i..16 * (i + 1)], v1);
    }
    if RATE % 16 != 0 {
        debug_assert!(RATE % 8 == 0);
        let i = (RATE / 8 - 1) / 5;
        let j = (RATE / 8 - 1) % 5;
        let mut u = [0u8; 16];
        _vst1q_bytes_u64(&mut u, s[i][j]);
        out[0][RATE - 8..RATE].copy_from_slice(&u[0..8]);
        out[1][RATE - 8..RATE].copy_from_slice(&u[8..16]);
    }
}

#[inline(always)]
pub(crate) fn store_block_full<const RATE: usize>(s: &[[uint64x2_t; 5]; 5]) -> [[u8; 200]; 2] {
    let mut out0 = [0u8; 200];
    let mut out1 = [0u8; 200];
    store_block::<RATE>(s, [&mut out0, &mut out1]);
    [out0, out1]
}

#[inline(always)]
fn slice_2(a: [&[u8]; 2], start: usize, len: usize) -> [&[u8]; 2] {
    [&a[0][start..start + len], &a[1][start..start + len]]
}

#[inline(always)]
fn split_at_mut_2(out: [&mut [u8]; 2], mid: usize) -> ([&mut [u8]; 2], [&mut [u8]; 2]) {
    let [out0, out1] = out;
    let (out00, out01) = out0.split_at_mut(mid);
    let (out10, out11) = out1.split_at_mut(mid);
    ([out00, out10], [out01, out11])
}

impl KeccakItem<2> for uint64x2_t {
    #[inline(always)]
    fn zero() -> Self {
        _vdupq_n_u64(0)
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
        _veorq_u64(a, b)
    }
    #[inline(always)]
    fn load_block<const RATE: usize>(a: &mut [[Self; 5]; 5], b: [&[u8]; 2]) {
        load_block::<RATE>(a, b)
    }
    #[inline(always)]
    fn store_block<const RATE: usize>(a: &[[Self; 5]; 5], b: [&mut [u8]; 2]) {
        store_block::<RATE>(a, b)
    }
    #[inline(always)]
    fn load_block_full<const RATE: usize>(a: &mut [[Self; 5]; 5], b: [[u8; 200]; 2]) {
        load_block_full::<RATE>(a, b)
    }
    #[inline(always)]
    fn store_block_full<const RATE: usize>(a: &[[Self; 5]; 5]) -> [[u8; 200]; 2] {
        store_block_full::<RATE>(a)
    }
    #[inline(always)]
    fn slice_n(a: [&[u8]; 2], start: usize, len: usize) -> [&[u8]; 2] {
        slice_2(a, start, len)
    }
    #[inline(always)]
    fn split_at_mut_n(a: [&mut [u8]; 2], mid: usize) -> ([&mut [u8]; 2], [&mut [u8]; 2]) {
        split_at_mut_2(a, mid)
    }

    // TODO: Do we need this, or not? cf. https://github.com/cryspen/libcrux/issues/482
    fn store<const RATE: usize>(_state: &[[Self; 5]; 5], _out: [&mut [u8]; 2]) {
        todo!()
    }
}
