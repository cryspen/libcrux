use libcrux_intrinsics::arm64::*;

use crate::traits::internal::{self, Block, Buffer, BufferMut, KeccakItem};

#[allow(non_camel_case_types)]
pub type uint64x2_t = _uint64x2_t;

#[derive(Clone, Copy)]
pub struct Buf<'a> {
    buf0: &'a [u8],
    buf1: &'a [u8],
}

impl<'a> internal::Buffer for Buf<'a> {
    fn len(&self) -> usize {
        self.buf0.len()
    }

    fn slice(&self, start: usize, len: usize) -> Self {
        Self {
            buf0: &self.buf0[start..start + len],
            buf1: &self.buf1[start..start + len],
        }
    }
}

pub struct BufMut<'a> {
    buf0: &'a mut [u8],
    buf1: &'a mut [u8],
}

impl<'a> BufferMut for BufMut<'a> {
    fn len(&self) -> usize {
        self.buf0.len()
    }

    fn slice_mut(self, mid: usize) -> (Self, Self) {
        let (first0, rest0) = self.buf0.split_at_mut(mid);
        let (first1, rest1) = self.buf1.split_at_mut(mid);
        (
            Self {
                buf0: first0,
                buf1: first1,
            },
            Self {
                buf0: rest0,
                buf1: rest1,
            },
        )
    }
}

/// A neon block. A simple wrapper around two `[u8; 200]`.
#[derive(Clone, Copy)]
pub struct FullBuf {
    buf0: [u8; 200],
    buf1: [u8; 200],

    /// The length of the original buffer.
    eob: usize,
}

impl<'a> internal::Block<Buf<'a>, BufMut<'a>> for FullBuf {
    fn init(b: Buf<'a>) -> Self {
        // XXX: This should load to intrinsics directly.
        let mut buf0 = [0u8; 200];
        let mut buf1 = [0u8; 200];
        let eob = b.len();
        if eob > 0 {
            buf0[0..b.len()].copy_from_slice(&b.buf0);
        }
        if eob > 0 {
            buf1[0..b.len()].copy_from_slice(&b.buf1);
        }
        Self { buf0, buf1, eob }
    }

    fn set_constants<const DELIM: u8, const EOB: usize>(&mut self) {
        self.buf0[self.eob] = DELIM;
        self.buf1[self.eob] = DELIM;

        self.buf0[EOB - 1] |= 0x80;
        self.buf1[EOB - 1] |= 0x80;
    }

    fn to_bytes(self, out: BufMut<'a>) {
        todo!()
    }
}

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
pub(crate) fn load_block<const BLOCK_SIZE: usize>(s: &mut [[uint64x2_t; 5]; 5], blocks: Buf) {
    debug_assert!(
        BLOCK_SIZE <= blocks.buf0.len()
            && BLOCK_SIZE % 8 == 0
            && blocks.buf0.len() == blocks.buf1.len()
    );
    for i in 0..BLOCK_SIZE / 16 {
        let v0 = _vld1q_bytes_u64(&blocks.buf0[16 * i..16 * (i + 1)]);
        let v1 = _vld1q_bytes_u64(&blocks.buf1[16 * i..16 * (i + 1)]);
        s[(2 * i) / 5][(2 * i) % 5] = _veorq_u64(s[(2 * i) / 5][(2 * i) % 5], _vtrn1q_u64(v0, v1));
        s[(2 * i + 1) / 5][(2 * i + 1) % 5] =
            _veorq_u64(s[(2 * i + 1) / 5][(2 * i + 1) % 5], _vtrn2q_u64(v0, v1));
    }
    if BLOCK_SIZE % 16 != 0 {
        let i = (BLOCK_SIZE / 8 - 1) / 5;
        let j = (BLOCK_SIZE / 8 - 1) % 5;
        let mut u = [0u64; 2];
        u[0] = u64::from_le_bytes(blocks.buf0[BLOCK_SIZE - 8..BLOCK_SIZE].try_into().unwrap());
        u[1] = u64::from_le_bytes(blocks.buf1[BLOCK_SIZE - 8..BLOCK_SIZE].try_into().unwrap());
        let uvec = _vld1q_u64(&u);
        s[i][j] = _veorq_u64(s[i][j], uvec);
    }
}

#[inline(always)]
pub(crate) fn load_block_full<const RATE: usize>(s: &mut [[uint64x2_t; 5]; 5], blocks: FullBuf) {
    load_block::<RATE>(
        s,
        Buf {
            buf0: &blocks.buf0,
            buf1: &blocks.buf1,
        },
    );
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(s: &[[uint64x2_t; 5]; 5], out: BufMut) {
    for i in 0..RATE / 16 {
        let v0 = _vtrn1q_u64(
            s[(2 * i) / 5][(2 * i) % 5],
            s[(2 * i + 1) / 5][(2 * i + 1) % 5],
        );
        let v1 = _vtrn2q_u64(
            s[(2 * i) / 5][(2 * i) % 5],
            s[(2 * i + 1) / 5][(2 * i + 1) % 5],
        );
        _vst1q_bytes_u64(&mut out.buf0[16 * i..16 * (i + 1)], v0);
        _vst1q_bytes_u64(&mut out.buf1[16 * i..16 * (i + 1)], v1);
    }
    if RATE % 16 != 0 {
        debug_assert!(RATE % 8 == 0);
        let i = (RATE / 8 - 1) / 5;
        let j = (RATE / 8 - 1) % 5;
        let mut u = [0u8; 16];
        _vst1q_bytes_u64(&mut u, s[i][j]);
        out.buf0[RATE - 8..RATE].copy_from_slice(&u[0..8]);
        out.buf1[RATE - 8..RATE].copy_from_slice(&u[8..16]);
    }
}

#[inline(always)]
pub(crate) fn store_block_full<const RATE: usize>(s: &[[uint64x2_t; 5]; 5]) -> FullBuf {
    let mut buf0 = [0u8; 200];
    let mut buf1 = [0u8; 200];
    todo!();
    // store_block::<RATE>(s, [&mut buf0, &mut buf1]);
    // FullBuf { buf0, buf1, eob: 0 }
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

impl<'a> KeccakItem<'a, 2> for uint64x2_t {
    type B = Buf<'a>;
    type Bm = BufMut<'a>;
    type Bl = FullBuf;

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
    fn load_block<const BLOCKSIZE: usize>(state: &mut [[Self; 5]; 5], buf: Buf) {
        load_block::<BLOCKSIZE>(state, buf)
    }
    #[inline(always)]
    fn store_block<const BLOCKSIZE: usize>(a: &[[Self; 5]; 5], b: BufMut) {
        store_block::<BLOCKSIZE>(a, b)
    }
    #[inline(always)]
    fn load_block_full<const BLOCKSIZE: usize>(state: &mut [[Self; 5]; 5], block: FullBuf) {
        load_block_full::<BLOCKSIZE>(state, block)
    }
    #[inline(always)]
    fn store_block_full<const BLOCKSIZE: usize>(state: &[[Self; 5]; 5]) -> FullBuf {
        store_block_full::<BLOCKSIZE>(state)
    }
    #[inline(always)]
    fn split_at_mut_n(a: [&mut [u8]; 2], mid: usize) -> ([&mut [u8]; 2], [&mut [u8]; 2]) {
        split_at_mut_2(a, mid)
    }
}
