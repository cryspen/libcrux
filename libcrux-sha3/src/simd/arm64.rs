use libcrux_intrinsics::arm64::*;

use crate::traits::{get_ij, internal::KeccakItem, set_ij};

#[allow(non_camel_case_types)]
pub type uint64x2_t = _uint64x2_t;

#[inline(always)]
fn _veor5q_u64(
    a: uint64x2_t,
    b: uint64x2_t,
    c: uint64x2_t,
    d: uint64x2_t,
    e: uint64x2_t,
) -> uint64x2_t {
    _veor3q_u64(_veor3q_u64(a, b, c), d, e)
}

#[inline(always)]
fn _vrax1q_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    libcrux_intrinsics::arm64::_vrax1q_u64(a, b)
}

#[inline(always)]
fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    libcrux_intrinsics::arm64::_vxarq_u64::<RIGHT>(a, b)
}

#[inline(always)]
fn _vbcaxq_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
    libcrux_intrinsics::arm64::_vbcaxq_u64(a, b, c)
}

#[inline(always)]
fn _veorq_n_u64(a: uint64x2_t, c: u64) -> uint64x2_t {
    let c = _vdupq_n_u64(c);
    _veorq_u64(a, c)
}

#[inline(always)]
pub(crate) fn load_block<const RATE: usize>(
    s: &mut [uint64x2_t; 25],
    blocks: &[&[u8]; 2],
    offset: usize,
) {
    debug_assert!(RATE <= blocks[0].len() && RATE % 8 == 0 && blocks[0].len() == blocks[1].len());
    for i in 0..RATE / 16 {
        let start = offset + 16 * i;
        let v0 = _vld1q_bytes_u64(&blocks[0][start..start + 16]);
        let v1 = _vld1q_bytes_u64(&blocks[1][start..start + 16]);
        let i0 = (2 * i) / 5;
        let j0 = (2 * i) % 5;
        let i1 = (2 * i + 1) / 5;
        let j1 = (2 * i + 1) % 5;
        set_ij(
            s,
            i0,
            j0,
            _veorq_u64(get_ij(s, i0, j0), _vtrn1q_u64(v0, v1)),
        );
        set_ij(
            s,
            i1,
            j1,
            _veorq_u64(get_ij(s, i1, j1), _vtrn2q_u64(v0, v1)),
        );
    }
    if RATE % 16 != 0 {
        let i = RATE / 8 - 1;
        let mut u = [0u64; 2];
        let start = offset + RATE - 8;
        u[0] = u64::from_le_bytes(blocks[0][start..start + 8].try_into().unwrap());
        u[1] = u64::from_le_bytes(blocks[1][start..start + 8].try_into().unwrap());
        let uvec = _vld1q_u64(&u);
        set_ij(s, i / 5, i % 5, _veorq_u64(get_ij(s, i / 5, i % 5), uvec));
    }
}

#[inline(always)]
pub(crate) fn load_block_full<const RATE: usize>(
    s: &mut [uint64x2_t; 25],
    blocks: &[[u8; 200]; 2],
    start: usize,
) {
    load_block::<RATE>(s, &[&blocks[0] as &[u8], &blocks[1] as &[u8]], start);
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(s: &[uint64x2_t; 25], out: &mut [&mut [u8]; 2]) {
    for i in 0..RATE / 16 {
        let i0 = (2 * i) / 5;
        let j0 = (2 * i) % 5;
        let i1 = (2 * i + 1) / 5;
        let j1 = (2 * i + 1) % 5;
        let v0 = _vtrn1q_u64(get_ij(s, i0, j0), get_ij(s, i1, j1));
        let v1 = _vtrn2q_u64(get_ij(s, i0, j0), get_ij(s, i1, j1));
        _vst1q_bytes_u64(&mut out[0][16 * i..16 * (i + 1)], v0);
        _vst1q_bytes_u64(&mut out[1][16 * i..16 * (i + 1)], v1);
    }
    if RATE % 16 != 0 {
        debug_assert!(RATE % 8 == 0);
        let i = RATE / 8 - 1;
        let mut u = [0u8; 16];
        _vst1q_bytes_u64(&mut u, get_ij(s, i / 5, i % 5));
        out[0][RATE - 8..RATE].copy_from_slice(&u[0..8]);
        out[1][RATE - 8..RATE].copy_from_slice(&u[8..16]);
    }
}

#[inline(always)]
pub(crate) fn store_block_full<const RATE: usize>(s: &[uint64x2_t; 25], out: &mut [[u8; 200]; 2]) {
    let (out0, out1) = out.split_at_mut(1);

    store_block::<RATE>(s, &mut [&mut out0[0], &mut out1[0]]);
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
    fn load_block<const RATE: usize>(state: &mut [Self; 25], blocks: &[&[u8]; 2], start: usize) {
        load_block::<RATE>(state, blocks, start)
    }
    #[inline(always)]
    fn store_block<const RATE: usize>(state: &[Self; 25], blocks: &mut [&mut [u8]; 2]) {
        store_block::<RATE>(state, blocks)
    }
    #[inline(always)]
    fn load_block_full<const RATE: usize>(
        state: &mut [Self; 25],
        blocks: &[[u8; 200]; 2],
        start: usize,
    ) {
        load_block_full::<RATE>(state, blocks, start)
    }
    #[inline(always)]
    fn store_block_full<const RATE: usize>(state: &[Self; 25], out: &mut [[u8; 200]; 2]) {
        store_block_full::<RATE>(state, out)
    }

    #[inline(always)]
    fn split_at_mut_n(a: [&mut [u8]; 2], mid: usize) -> ([&mut [u8]; 2], [&mut [u8]; 2]) {
        split_at_mut_2(a, mid)
    }

    // TODO: Do we need this, or not? cf. https://github.com/cryspen/libcrux/issues/482
    fn store<const RATE: usize>(_state: &[Self; 25], _out: [&mut [u8]; 2]) {
        todo!()
    }
}
