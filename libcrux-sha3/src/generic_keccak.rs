//! The generic SHA3 implementation that uses portable or platform specific
//! sub-routines.

use core::{marker::PhantomData, ops::Index};

use internal::{Block, Buffer, BufferMut};

use crate::traits::*;

#[cfg_attr(hax, hax_lib::opaque_type)]
#[derive(Clone, Copy)]
pub(crate) struct KeccakState<'a, T: KeccakStateItem<'a>> {
    st: [[T; 5]; 5],
    phantom: PhantomData<&'a ()>,
}

impl<'a, T: KeccakStateItem<'a>> Index<usize> for KeccakState<'a, T> {
    type Output = [T; 5];

    fn index(&self, index: usize) -> &Self::Output {
        &self.st[index]
    }
}

impl<'a, T: KeccakStateItem<'a>> KeccakState<'a, T> {
    /// Create a new Shake128 x4 state.
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self {
            st: [[T::zero(); 5]; 5],
            phantom: PhantomData,
        }
    }
}

/// From here, everything is generic
///
const _ROTC: [usize; 24] = [
    1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

#[inline(always)]
pub(crate) fn theta_rho<'a, T: KeccakStateItem<'a>>(s: &mut KeccakState<'a, T>) {
    let c: [T; 5] = [
        T::xor5(s.st[0][0], s.st[1][0], s.st[2][0], s.st[3][0], s.st[4][0]),
        T::xor5(s.st[0][1], s.st[1][1], s.st[2][1], s.st[3][1], s.st[4][1]),
        T::xor5(s.st[0][2], s.st[1][2], s.st[2][2], s.st[3][2], s.st[4][2]),
        T::xor5(s.st[0][3], s.st[1][3], s.st[2][3], s.st[3][3], s.st[4][3]),
        T::xor5(s.st[0][4], s.st[1][4], s.st[2][4], s.st[3][4], s.st[4][4]),
    ];
    #[allow(clippy::identity_op)]
    let t: [T; 5] = [
        T::rotate_left1_and_xor(c[(0 + 4) % 5], c[(0 + 1) % 5]),
        T::rotate_left1_and_xor(c[(1 + 4) % 5], c[(1 + 1) % 5]),
        T::rotate_left1_and_xor(c[(2 + 4) % 5], c[(2 + 1) % 5]),
        T::rotate_left1_and_xor(c[(3 + 4) % 5], c[(3 + 1) % 5]),
        T::rotate_left1_and_xor(c[(4 + 4) % 5], c[(4 + 1) % 5]),
    ];

    s.st[0][0] = T::xor(s.st[0][0], t[0]);
    s.st[1][0] = T::xor_and_rotate::<36, 28>(s.st[1][0], t[0]);
    s.st[2][0] = T::xor_and_rotate::<3, 61>(s.st[2][0], t[0]);
    s.st[3][0] = T::xor_and_rotate::<41, 23>(s.st[3][0], t[0]);
    s.st[4][0] = T::xor_and_rotate::<18, 46>(s.st[4][0], t[0]);

    s.st[0][1] = T::xor_and_rotate::<1, 63>(s.st[0][1], t[1]);
    s.st[1][1] = T::xor_and_rotate::<44, 20>(s.st[1][1], t[1]);
    s.st[2][1] = T::xor_and_rotate::<10, 54>(s.st[2][1], t[1]);
    s.st[3][1] = T::xor_and_rotate::<45, 19>(s.st[3][1], t[1]);
    s.st[4][1] = T::xor_and_rotate::<2, 62>(s.st[4][1], t[1]);

    s.st[0][2] = T::xor_and_rotate::<62, 2>(s.st[0][2], t[2]);
    s.st[1][2] = T::xor_and_rotate::<6, 58>(s.st[1][2], t[2]);
    s.st[2][2] = T::xor_and_rotate::<43, 21>(s.st[2][2], t[2]);
    s.st[3][2] = T::xor_and_rotate::<15, 49>(s.st[3][2], t[2]);
    s.st[4][2] = T::xor_and_rotate::<61, 3>(s.st[4][2], t[2]);

    s.st[0][3] = T::xor_and_rotate::<28, 36>(s.st[0][3], t[3]);
    s.st[1][3] = T::xor_and_rotate::<55, 9>(s.st[1][3], t[3]);
    s.st[2][3] = T::xor_and_rotate::<25, 39>(s.st[2][3], t[3]);
    s.st[3][3] = T::xor_and_rotate::<21, 43>(s.st[3][3], t[3]);
    s.st[4][3] = T::xor_and_rotate::<56, 8>(s.st[4][3], t[3]);

    s.st[0][4] = T::xor_and_rotate::<27, 37>(s.st[0][4], t[4]);
    s.st[1][4] = T::xor_and_rotate::<20, 44>(s.st[1][4], t[4]);
    s.st[2][4] = T::xor_and_rotate::<39, 25>(s.st[2][4], t[4]);
    s.st[3][4] = T::xor_and_rotate::<8, 56>(s.st[3][4], t[4]);
    s.st[4][4] = T::xor_and_rotate::<14, 50>(s.st[4][4], t[4]);
}

const _PI: [usize; 24] = [
    6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21,
];

#[inline(always)]
pub(crate) fn pi<'a, T: KeccakStateItem<'a>>(s: &mut KeccakState<'a, T>) {
    let old = s.st;
    s.st[0][1] = old[1][1];
    s.st[0][2] = old[2][2];
    s.st[0][3] = old[3][3];
    s.st[0][4] = old[4][4];
    s.st[1][0] = old[0][3];
    s.st[1][1] = old[1][4];
    s.st[1][2] = old[2][0];
    s.st[1][3] = old[3][1];
    s.st[1][4] = old[4][2];
    s.st[2][0] = old[0][1];
    s.st[2][1] = old[1][2];
    s.st[2][2] = old[2][3];
    s.st[2][3] = old[3][4];
    s.st[2][4] = old[4][0];
    s.st[3][0] = old[0][4];
    s.st[3][1] = old[1][0];
    s.st[3][2] = old[2][1];
    s.st[3][3] = old[3][2];
    s.st[3][4] = old[4][3];
    s.st[4][0] = old[0][2];
    s.st[4][1] = old[1][3];
    s.st[4][2] = old[2][4];
    s.st[4][3] = old[3][0];
    s.st[4][4] = old[4][1];
}

#[inline(always)]
pub(crate) fn chi<'a, T: KeccakStateItem<'a>>(s: &mut KeccakState<'a, T>) {
    let old = s.st;

    #[allow(clippy::needless_range_loop)]
    for i in 0..5 {
        for j in 0..5 {
            s.st[i][j] = T::and_not_xor(s.st[i][j], old[i][(j + 2) % 5], old[i][(j + 1) % 5]);
        }
    }
}

const ROUNDCONSTANTS: [u64; 24] = [
    0x0000_0000_0000_0001u64,
    0x0000_0000_0000_8082u64,
    0x8000_0000_0000_808au64,
    0x8000_0000_8000_8000u64,
    0x0000_0000_0000_808bu64,
    0x0000_0000_8000_0001u64,
    0x8000_0000_8000_8081u64,
    0x8000_0000_0000_8009u64,
    0x0000_0000_0000_008au64,
    0x0000_0000_0000_0088u64,
    0x0000_0000_8000_8009u64,
    0x0000_0000_8000_000au64,
    0x0000_0000_8000_808bu64,
    0x8000_0000_0000_008bu64,
    0x8000_0000_0000_8089u64,
    0x8000_0000_0000_8003u64,
    0x8000_0000_0000_8002u64,
    0x8000_0000_0000_0080u64,
    0x0000_0000_0000_800au64,
    0x8000_0000_8000_000au64,
    0x8000_0000_8000_8081u64,
    0x8000_0000_0000_8080u64,
    0x0000_0000_8000_0001u64,
    0x8000_0000_8000_8008u64,
];

#[inline(always)]
pub(crate) fn iota<'a, T: KeccakStateItem<'a>>(s: &mut KeccakState<'a, T>, i: usize) {
    s.st[0][0] = T::xor_constant(s.st[0][0], ROUNDCONSTANTS[i]);
}

#[inline(always)]
pub(crate) fn keccakf1600<'a, T: KeccakStateItem<'a>>(s: &mut KeccakState<'a, T>) {
    for i in 0..24 {
        theta_rho(s);
        pi(s);
        chi(s);
        iota(s, i);
    }
}

#[inline(always)]
pub(crate) fn absorb_block<'a, T: KeccakStateItem<'a>, const RATE: usize>(
    s: &mut KeccakState<'a, T>,
    blocks: T::B,
) {
    T::load_block::<RATE>(&mut s.st, blocks);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn absorb_final<'a, T: KeccakStateItem<'a>, const RATE: usize, const DELIM: u8>(
    s: &mut KeccakState<'a, T>,
    last: T::B,
) {
    debug_assert!(last.len() < RATE);
    // XXX: This could also be done with function pointers to reducing code size.
    let mut last_block = T::Bl::init(last);
    last_block.set_constants::<DELIM, RATE>();
    T::load_block_full::<RATE>(&mut s.st, last_block);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn squeeze_first_block<'a, T: KeccakStateItem<'a>, const RATE: usize>(
    s: &KeccakState<'a, T>,
    out: T::Bm,
) {
    T::store_block::<RATE>(&s.st, out)
}

#[inline(always)]
pub(crate) fn squeeze_next_block<'a, T: KeccakStateItem<'a>, const RATE: usize>(
    s: &mut KeccakState<'a, T>,
    out: T::Bm,
) {
    keccakf1600(s);
    T::store_block::<RATE>(&s.st, out)
}

#[inline(always)]
pub(crate) fn squeeze_first_three_blocks<'a, T: KeccakStateItem<'a>, const BLOCK_SIZE: usize>(
    s: &mut KeccakState<'a, T>,
    out: T::Bm,
) {
    let (o0, o1) = out.slice_mut(BLOCK_SIZE);
    squeeze_first_block::<T, BLOCK_SIZE>(s, o0);
    let (o1, o2) = o1.slice_mut(BLOCK_SIZE);
    squeeze_next_block::<T, BLOCK_SIZE>(s, o1);
    squeeze_next_block::<T, BLOCK_SIZE>(s, o2);
}

#[inline(always)]
pub(crate) fn squeeze_first_five_blocks<'a, T: KeccakStateItem<'a>, const BLOCK_SIZE: usize>(
    s: &mut KeccakState<'a, T>,
    out: T::Bm,
) {
    let (o0, o1) = out.slice_mut(BLOCK_SIZE);
    squeeze_first_block::<T, BLOCK_SIZE>(s, o0);
    let (o1, o2) = o1.slice_mut(BLOCK_SIZE);

    squeeze_next_block::<T, BLOCK_SIZE>(s, o1);
    let (o2, o3) = o2.slice_mut(BLOCK_SIZE);

    squeeze_next_block::<T, BLOCK_SIZE>(s, o2);
    let (o3, o4) = o3.slice_mut(BLOCK_SIZE);

    squeeze_next_block::<T, BLOCK_SIZE>(s, o3);
    squeeze_next_block::<T, BLOCK_SIZE>(s, o4);
}

#[inline(always)]
pub(crate) fn squeeze_last<'a, T: KeccakStateItem<'a>, const RATE: usize>(
    mut s: KeccakState<'a, T>,
    out: T::Bm,
) {
    keccakf1600(&mut s);
    let b = T::store_block_full::<RATE>(&s.st);
    b.to_bytes(out);
}

#[inline(always)]
pub(crate) fn squeeze_first_and_last<'a, T: KeccakStateItem<'a>, const RATE: usize>(
    s: &KeccakState<'a, T>,
    out: T::Bm,
) {
    let b = T::store_block_full::<RATE>(&s.st);
    b.to_bytes(out);
}

#[inline(always)]
pub(crate) fn keccak<'a, T: KeccakStateItem<'a>, const BLOCK_SIZE: usize, const DELIM: u8>(
    data: T::B,
    out: T::Bm,
) {
    let mut s = KeccakState::<T>::new();
    for i in 0..data.len() / BLOCK_SIZE {
        absorb_block::<T, BLOCK_SIZE>(&mut s, data.slice(i * BLOCK_SIZE, BLOCK_SIZE));
    }
    let rem = data.len() % BLOCK_SIZE;
    absorb_final::<T, BLOCK_SIZE, DELIM>(&mut s, data.slice(data.len() - rem, rem));

    let outlen = out.len();
    let blocks = outlen / BLOCK_SIZE;
    let last = outlen - (outlen % BLOCK_SIZE);

    if blocks == 0 {
        squeeze_first_and_last::<T, BLOCK_SIZE>(&s, out)
    } else {
        // let (o0, mut o1) = T::split_at_mut_n(out, RATE);
        let (out0, mut out_rest) = out.slice_mut(BLOCK_SIZE);
        squeeze_first_block::<T, BLOCK_SIZE>(&s, out0);
        for _i in 1..blocks {
            let (o, o_rest) = out_rest.slice_mut(BLOCK_SIZE);
            squeeze_next_block::<T, BLOCK_SIZE>(&mut s, o);
            out_rest = o_rest;
        }
        if last < outlen {
            squeeze_last::<T, BLOCK_SIZE>(s, out_rest)
        }
    }
}
