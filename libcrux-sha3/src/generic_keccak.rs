//! The generic SHA3 implementation that uses portable or platform specific
//! sub-routines.

use core::ops::Index;

use crate::traits::{get_ij, set_ij, KeccakStateItem};

/// A generic Xof API.
pub(crate) mod xof;

#[cfg_attr(hax, hax_lib::opaque)]
#[derive(Clone, Copy)]
pub(crate) struct KeccakState<const N: usize, T: KeccakStateItem<N>> {
    st: [T; 25],
}

impl<const N: usize, T: KeccakStateItem<N>> KeccakState<N, T> {}

impl<const N: usize, T: KeccakStateItem<N>> KeccakState<N, T> {
    /// Create a new Shake128 x4 state.
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self {
            st: [T::zero(); 25],
        }
    }

    /// Set element `[i, j] = v`.
    fn set(&mut self, i: usize, j: usize, v: T) {
        set_ij(&mut self.st, i, j, v);
    }
}

impl<const N: usize, T: KeccakStateItem<N>> Index<(usize, usize)> for KeccakState<N, T> {
    type Output = T;

    /// Get element `[i, j]`.
    fn index(&self, index: (usize, usize)) -> &Self::Output {
        get_ij(&self.st, index.0, index.1)
    }
}

#[inline(always)]
pub(crate) fn theta_rho<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>) {
    let c: [T; 5] = [
        T::xor5(s[(0, 0)], s[(1, 0)], s[(2, 0)], s[(3, 0)], s[(4, 0)]),
        T::xor5(s[(0, 1)], s[(1, 1)], s[(2, 1)], s[(3, 1)], s[(4, 1)]),
        T::xor5(s[(0, 2)], s[(1, 2)], s[(2, 2)], s[(3, 2)], s[(4, 2)]),
        T::xor5(s[(0, 3)], s[(1, 3)], s[(2, 3)], s[(3, 3)], s[(4, 3)]),
        T::xor5(s[(0, 4)], s[(1, 4)], s[(2, 4)], s[(3, 4)], s[(4, 4)]),
    ];
    #[allow(clippy::identity_op)]
    let t: [T; 5] = [
        T::rotate_left1_and_xor(c[(0 + 4) % 5], c[(0 + 1) % 5]),
        T::rotate_left1_and_xor(c[(1 + 4) % 5], c[(1 + 1) % 5]),
        T::rotate_left1_and_xor(c[(2 + 4) % 5], c[(2 + 1) % 5]),
        T::rotate_left1_and_xor(c[(3 + 4) % 5], c[(3 + 1) % 5]),
        T::rotate_left1_and_xor(c[(4 + 4) % 5], c[(4 + 1) % 5]),
    ];

    s.set(0, 0, T::xor(s[(0, 0)], t[0]));
    s.set(1, 0, T::xor_and_rotate::<36, 28>(s[(1, 0)], t[0]));
    s.set(2, 0, T::xor_and_rotate::<3, 61>(s[(2, 0)], t[0]));
    s.set(3, 0, T::xor_and_rotate::<41, 23>(s[(3, 0)], t[0]));
    s.set(4, 0, T::xor_and_rotate::<18, 46>(s[(4, 0)], t[0]));

    s.set(0, 1, T::xor_and_rotate::<1, 63>(s[(0, 1)], t[1]));
    s.set(1, 1, T::xor_and_rotate::<44, 20>(s[(1, 1)], t[1]));
    s.set(2, 1, T::xor_and_rotate::<10, 54>(s[(2, 1)], t[1]));
    s.set(3, 1, T::xor_and_rotate::<45, 19>(s[(3, 1)], t[1]));
    s.set(4, 1, T::xor_and_rotate::<2, 62>(s[(4, 1)], t[1]));

    s.set(0, 2, T::xor_and_rotate::<62, 2>(s[(0, 2)], t[2]));
    s.set(1, 2, T::xor_and_rotate::<6, 58>(s[(1, 2)], t[2]));
    s.set(2, 2, T::xor_and_rotate::<43, 21>(s[(2, 2)], t[2]));
    s.set(3, 2, T::xor_and_rotate::<15, 49>(s[(3, 2)], t[2]));
    s.set(4, 2, T::xor_and_rotate::<61, 3>(s[(4, 2)], t[2]));

    s.set(0, 3, T::xor_and_rotate::<28, 36>(s[(0, 3)], t[3]));
    s.set(1, 3, T::xor_and_rotate::<55, 9>(s[(1, 3)], t[3]));
    s.set(2, 3, T::xor_and_rotate::<25, 39>(s[(2, 3)], t[3]));
    s.set(3, 3, T::xor_and_rotate::<21, 43>(s[(3, 3)], t[3]));
    s.set(4, 3, T::xor_and_rotate::<56, 8>(s[(4, 3)], t[3]));

    s.set(0, 4, T::xor_and_rotate::<27, 37>(s[(0, 4)], t[4]));
    s.set(1, 4, T::xor_and_rotate::<20, 44>(s[(1, 4)], t[4]));
    s.set(2, 4, T::xor_and_rotate::<39, 25>(s[(2, 4)], t[4]));
    s.set(3, 4, T::xor_and_rotate::<8, 56>(s[(3, 4)], t[4]));
    s.set(4, 4, T::xor_and_rotate::<14, 50>(s[(4, 4)], t[4]));
}

const _PI: [usize; 24] = [
    6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21,
];

#[inline(always)]
pub(crate) fn pi<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>) {
    let old = s.clone();
    s.set(1, 0, old[(0, 3)]);
    s.set(2, 0, old[(0, 1)]);
    s.set(3, 0, old[(0, 4)]);
    s.set(4, 0, old[(0, 2)]);
    s.set(0, 1, old[(1, 1)]);
    s.set(1, 1, old[(1, 4)]);
    s.set(2, 1, old[(1, 2)]);
    s.set(3, 1, old[(1, 0)]);
    s.set(4, 1, old[(1, 3)]);
    s.set(0, 2, old[(2, 2)]);
    s.set(1, 2, old[(2, 0)]);
    s.set(2, 2, old[(2, 3)]);
    s.set(3, 2, old[(2, 1)]);
    s.set(4, 2, old[(2, 4)]);
    s.set(0, 3, old[(3, 3)]);
    s.set(1, 3, old[(3, 1)]);
    s.set(2, 3, old[(3, 4)]);
    s.set(3, 3, old[(3, 2)]);
    s.set(4, 3, old[(3, 0)]);
    s.set(0, 4, old[(4, 4)]);
    s.set(1, 4, old[(4, 2)]);
    s.set(2, 4, old[(4, 0)]);
    s.set(3, 4, old[(4, 3)]);
    s.set(4, 4, old[(4, 1)]);
}

#[inline(always)]
pub(crate) fn chi<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>) {
    let old = s.clone();

    #[allow(clippy::needless_range_loop)]
    for i in 0..5 {
        for j in 0..5 {
            s.set(
                i,
                j,
                T::and_not_xor(s[(i, j)], old[(i, (j + 2) % 5)], old[(i, (j + 1) % 5)]),
            );
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
pub(crate) fn iota<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>, i: usize) {
    s.set(0, 0, T::xor_constant(s[(0, 0)], ROUNDCONSTANTS[i]));
}

#[inline(always)]
pub(crate) fn keccakf1600<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>) {
    for i in 0..24 {
        theta_rho(s);
        pi(s);
        chi(s);
        iota(s, i);
    }
}

#[inline(always)]
pub(crate) fn absorb_block<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &mut KeccakState<N, T>,
    blocks: &[&[u8]; N],
    start: usize,
) {
    T::load_block::<RATE>(&mut s.st, blocks, start);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn absorb_final<
    const N: usize,
    T: KeccakStateItem<N>,
    const RATE: usize,
    const DELIM: u8,
>(
    s: &mut KeccakState<N, T>,
    last: &[&[u8]; N],
    start: usize,
    len: usize,
) {
    debug_assert!(N > 0 && len < RATE);

    T::load_last::<RATE, DELIM>(&mut s.st, last, start, len);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn squeeze_first_block<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &KeccakState<N, T>,
    out: &mut [&mut [u8]; N],
) {
    T::store_block::<RATE>(&s.st, out, 0, RATE)
}

#[inline(always)]
pub(crate) fn squeeze_next_block<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &mut KeccakState<N, T>,
    out: &mut [&mut [u8]; N],
    start: usize,
) {
    keccakf1600(s);
    T::store_block::<RATE>(&s.st, out, start, RATE)
}

#[inline(always)]
pub(crate) fn squeeze_last<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    mut s: KeccakState<N, T>,
    out: &mut [&mut [u8]; N],
    start: usize,
    len: usize,
) {
    keccakf1600(&mut s);
    T::store_block::<RATE>(&s.st, out, start, len);
}

#[inline(always)]
pub(crate) fn squeeze_first_and_last<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &KeccakState<N, T>,
    out: &mut [&mut [u8]; N],
    start: usize,
    len: usize,
) {
    T::store_block::<RATE>(&s.st, out, start, len);
}

#[inline]
pub(crate) fn keccak<const N: usize, T: KeccakStateItem<N>, const RATE: usize, const DELIM: u8>(
    data: &[&[u8]; N],
    mut out: [&mut [u8]; N],
) {
    let mut s = KeccakState::<N, T>::new();
    for i in 0..data[0].len() / RATE {
        absorb_block::<N, T, RATE>(&mut s, &data, i * RATE);
    }
    let rem = data[0].len() % RATE;
    absorb_final::<N, T, RATE, DELIM>(&mut s, data, data[0].len() - rem, rem);

    let outlen = out[0].len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    if blocks == 0 {
        squeeze_first_and_last::<N, T, RATE>(&s, &mut out, 0, outlen)
    } else {
        squeeze_first_block::<N, T, RATE>(&s, &mut out);
        for i in 1..blocks {
            squeeze_next_block::<N, T, RATE>(&mut s, &mut out, i * RATE);
        }
        if last < outlen {
            squeeze_last::<N, T, RATE>(s, &mut out, last, outlen - last);
        }
    }
}

/// Squeeze multiple blocks at once.
///
/// These are useful for ML-KEM and ML-DSA implementations.
pub(crate) mod multi_squeeze {
    use super::*;

    #[inline(always)]
    pub(crate) fn squeeze_first_three_blocks<
        const N: usize,
        T: KeccakStateItem<N>,
        const RATE: usize,
    >(
        s: &mut KeccakState<N, T>,
        out: &mut [&mut [u8]; N],
    ) {
        squeeze_first_block::<N, T, RATE>(s, out);
        squeeze_next_block::<N, T, RATE>(s, out, RATE);
        squeeze_next_block::<N, T, RATE>(s, out, 2 * RATE);
    }

    #[inline(always)]
    pub(crate) fn squeeze_first_five_blocks<
        const N: usize,
        T: KeccakStateItem<N>,
        const RATE: usize,
    >(
        s: &mut KeccakState<N, T>,
        out: &mut [&mut [u8]; N],
    ) {
        squeeze_first_block::<N, T, RATE>(s, out);
        squeeze_next_block::<N, T, RATE>(s, out, RATE);
        squeeze_next_block::<N, T, RATE>(s, out, 2 * RATE);
        squeeze_next_block::<N, T, RATE>(s, out, 3 * RATE);
        squeeze_next_block::<N, T, RATE>(s, out, 4 * RATE);
    }
}
