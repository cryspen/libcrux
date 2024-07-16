//! The generic SHA3 implementation that uses portable or platform specific
//! sub-routines.

use core::ops::Index;

use crate::traits::*;

#[cfg_attr(hax, hax_lib::opaque_type)]
#[derive(Clone, Copy)]
pub(crate) struct KeccakState<const N: usize, T: KeccakStateItem<N>> {
    st: [[T; 5]; 5],
}

impl<const N: usize, T: KeccakStateItem<N>> Index<usize> for KeccakState<N, T> {
    type Output = [T; 5];

    fn index(&self, index: usize) -> &Self::Output {
        &self.st[index]
    }
}

impl<const N: usize, T: KeccakStateItem<N>> KeccakState<N, T> {
    /// Create a new Shake128 x4 state.
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self {
            st: [[T::zero(); 5]; 5],
        }
    }
}

/// An abstraction for abstraction a block.
///
/// This holds `N` references to byte slices that are being processed.
pub(crate) struct Block<'a, const N: usize> {
    blocks: [&'a [u8]; N],
}

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs.
#[cfg_attr(hax, hax_lib::opaque_type)]
#[derive(Clone, Copy)]
pub(crate) struct KeccakXofState<const N: usize, const RATE: usize, T: KeccakStateItem<N>> {
    inner: KeccakState<N, T>,

    // Buffer inputs on absorb.
    buf: [[u8; RATE]; N],

    // Buffered length.
    buf_len: usize,

    // Needs sponge.
    sponge: bool,
}

impl<const N: usize, const RATE: usize, T: KeccakStateItem<N>> KeccakXofState<N, RATE, T> {
    /// Generate a new keccak xof state.
    pub(crate) fn new() -> Self {
        Self {
            inner: KeccakState::new(),
            buf: [[0; RATE]; N],
            buf_len: 0,
            sponge: false,
        }
    }

    /// Absorb
    ///
    /// This function takes any number of bytes to absorb and buffers if it's not enough.
    /// The function assumes that all input slices in `blocks` have the same length.
    ///
    /// Only a multiple of `RATE` blocks are absorbed.
    /// For the remaining bytes [`absorb_final`] needs to be called.
    ///
    /// This works best with relatively small `inputs`.
    #[inline(always)]
    pub(crate) fn absorb(&mut self, inputs: [&[u8]; N]) {
        let input_len = inputs[0].len();

        debug_assert!(N > 0);
        debug_assert!(self.buf_len < RATE);
        #[cfg(debug_assertions)]
        {
            for block in inputs {
                debug_assert!(block.len() == input_len);
            }
        }

        // Check if there are buffered bytes to absorb first and consume them.
        let input_consumed = self.consume_buffer(input_len, inputs);

        // Consume the (rest of the) input ...
        for i in 0..input_len / RATE {
            // We only get in here if `input_len / RATE > 0`.
            T::load_block::<RATE>(
                &mut self.inner.st,
                T::slice_n(inputs, input_consumed * RATE + i * RATE, RATE),
            );
            keccakf1600(&mut self.inner);
        }
        // ... and buffer the rest if there's not enough input (left).
        if input_len - input_consumed < RATE && input_len > input_consumed {
            for i in 0..N {
                self.buf[i][input_consumed..input_len].copy_from_slice(inputs[i]);
            }
        }
    }

    /// Consume the internal buffer and the required amount of the input to pad to
    /// `RATE`.
    ///
    /// Returns the `consumed` amount of bytes from `inputs`.
    fn consume_buffer(&mut self, input_len: usize, inputs: [&[u8]; N]) -> usize {
        let mut consumed = 0;
        if self.buf_len > 0 {
            if self.buf_len + input_len >= RATE {
                consumed = RATE - self.buf_len;
                // We have enough to absorb something.
                // XXX: This could be done more efficiently when we absorb from blocks
                //      rather than concat them first.
                let mut blocks = [[0u8; RATE]; N];
                for i in 0..N {
                    blocks[i][0..self.buf_len].copy_from_slice(&self.buf[i]);
                    blocks[i][self.buf_len..].copy_from_slice(&inputs[i][..consumed])
                }
                let borrowed: [&[u8]; N] = core::array::from_fn(|i| &blocks[i] as &[u8]);
                T::load_block::<RATE>(&mut self.inner.st, borrowed);
                keccakf1600(&mut self.inner);

                // Now we absorbed the buffered bytes and the part of the inputs to
                // fill up to `RATE`.
                // Consume the rest of the inputs that we can and store the rest
                // in the buffer
                self.buf_len = 0;
            }
        }
        consumed
    }
    /// Absorb a final block.
    ///
    /// The `inputs` block may be empty. Everything in the `inputs` block beyond
    /// `RATE` bytes is ignored.
    #[inline(always)]
    pub(crate) fn absorb_final<const DELIM: u8>(&mut self, inputs: [&[u8]; N]) {
        debug_assert!(N > 0 && inputs[0].len() < RATE);
        let input_len = inputs[0].len();

        debug_assert!(N > 0);
        debug_assert!(self.buf_len < RATE);
        #[cfg(debug_assertions)]
        {
            for block in inputs {
                debug_assert!(block.len() == input_len);
            }
        }

        // Check if there are buffered bytes to absorb first and consume them.
        let consumed = self.consume_buffer(input_len, inputs);

        // Consume the remaining bytes.
        let mut blocks = [[0u8; 200]; N];
        for i in 0..N {
            blocks[i][0..input_len].copy_from_slice(&inputs[i][consumed..]);
            blocks[i][input_len] = DELIM;
            blocks[i][RATE - 1] |= 0x80;
        }
        T::load_block_full::<RATE>(&mut self.inner.st, blocks);
        keccakf1600(&mut self.inner);
    }

    /// Squeeze `N` x `LEN` bytes.
    #[inline(always)]
    pub(crate) fn squeeze(&mut self, out: [&mut [u8]; N]) {
        if self.sponge {
            keccakf1600(&mut self.inner);
        }

        // We need a larger buffer to squeeze into.
        // XXX: This could be done more efficiently.

        let mut buf = [[0u8; RATE]; N];
        // let out_buf: [&mut [u8]; N] = core::array::from_fn(|i| &mut buf[i] as &mut [u8]);
        T::store::<RATE>(&self.inner.st, out_buf);
        self.sponge = true;
    }
}

impl<'a, const N: usize> Block<'a, N> {
    /// Build a block.
    pub(crate) fn new(blocks: [&'a [u8]; N]) -> Self {
        // XXX: This should really return a result
        #[cfg(debug_assertions)]
        let len = blocks[0].len();
        for block in blocks {
            debug_assert!(block.len() == len);
        }

        Self { blocks }
    }

    pub(crate) fn len(&self) -> usize {
        self.blocks[0].len()
    }

    pub(crate) fn get(&'a self, i: usize) -> &'a [u8] {
        self.blocks[i]
    }
}

impl<'a, const N: usize> Index<usize> for Block<'a, N> {
    type Output = [u8];

    fn index(&self, index: usize) -> &Self::Output {
        self.blocks[index]
    }
}

impl<'a, const N: usize> From<[&'a [u8]; N]> for Block<'a, N> {
    fn from(blocks: [&'a [u8]; N]) -> Self {
        Self { blocks }
    }
}

/// An abstraction for abstraction a block.
///
/// This holds `N` references to mutable byte slices that are being processed.
pub(crate) struct BlockMut<'a, const N: usize> {
    blocks: [&'a mut [u8]; N],
}

impl<'a, const N: usize> BlockMut<'a, N> {
    /// Create a new mutable block
    pub(crate) fn new(blocks: [&'a mut [u8]; N]) -> Self {
        Self { blocks }
    }

    /// Get a mutable element
    pub(crate) fn get_mut(&'a mut self, i: usize) -> &'a mut [u8] {
        self.blocks[i]
    }
}

/// From here, everything is generic
///
const _ROTC: [usize; 24] = [
    1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

#[inline(always)]
pub(crate) fn theta_rho<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>) {
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
pub(crate) fn pi<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>) {
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
pub(crate) fn chi<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>) {
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
pub(crate) fn iota<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>, i: usize) {
    s.st[0][0] = T::xor_constant(s.st[0][0], ROUNDCONSTANTS[i]);
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
    blocks: [&[u8]; N],
) {
    T::load_block::<RATE>(&mut s.st, blocks);
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
    last: Block<N>,
) {
    debug_assert!(N > 0 && last.len() < RATE);
    let last_len = last.len();
    let mut blocks = [[0u8; 200]; N];
    for i in 0..N {
        blocks[i][0..last_len].copy_from_slice(&last[i]);
        blocks[i][last_len] = DELIM;
        blocks[i][RATE - 1] |= 0x80;
    }
    T::load_block_full::<RATE>(&mut s.st, blocks);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn squeeze_first_block<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &KeccakState<N, T>,
    out: [&mut [u8]; N],
) {
    T::store_block::<RATE>(&s.st, out)
}

#[inline(always)]
pub(crate) fn squeeze_next_block<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &mut KeccakState<N, T>,
    out: [&mut [u8]; N],
) {
    keccakf1600(s);
    T::store_block::<RATE>(&s.st, out)
}

#[inline(always)]
pub(crate) fn squeeze_first_three_blocks<
    const N: usize,
    T: KeccakStateItem<N>,
    const RATE: usize,
>(
    s: &mut KeccakState<N, T>,
    out: [&mut [u8]; N],
) {
    let (o0, o1) = T::split_at_mut_n(out, RATE);
    squeeze_first_block::<N, T, RATE>(s, o0);
    let (o1, o2) = T::split_at_mut_n(o1, RATE);
    squeeze_next_block::<N, T, RATE>(s, o1);
    squeeze_next_block::<N, T, RATE>(s, o2);
}

#[inline(always)]
pub(crate) fn squeeze_first_five_blocks<
    const N: usize,
    T: KeccakStateItem<N>,
    const RATE: usize,
>(
    s: &mut KeccakState<N, T>,
    out: [&mut [u8]; N],
) {
    let (o0, o1) = T::split_at_mut_n(out, RATE);
    squeeze_first_block::<N, T, RATE>(s, o0);
    let (o1, o2) = T::split_at_mut_n(o1, RATE);

    squeeze_next_block::<N, T, RATE>(s, o1);
    let (o2, o3) = T::split_at_mut_n(o2, RATE);

    squeeze_next_block::<N, T, RATE>(s, o2);
    let (o3, o4) = T::split_at_mut_n(o3, RATE);

    squeeze_next_block::<N, T, RATE>(s, o3);
    squeeze_next_block::<N, T, RATE>(s, o4);
}

#[inline(always)]
pub(crate) fn squeeze_last<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    mut s: KeccakState<N, T>,
    out: [&mut [u8]; N],
) {
    keccakf1600(&mut s);
    let b = T::store_block_full::<RATE>(&s.st);
    for i in 0..N {
        out[i].copy_from_slice(&b[i][0..out[i].len()]);
    }
}

#[inline(always)]
pub(crate) fn squeeze_first_and_last<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &KeccakState<N, T>,
    out: [&mut [u8]; N],
) {
    let b = T::store_block_full::<RATE>(&s.st);
    for i in 0..N {
        out[i].copy_from_slice(&b[i][0..out[i].len()]);
    }
}

#[inline(always)]
pub(crate) fn keccak<const N: usize, T: KeccakStateItem<N>, const RATE: usize, const DELIM: u8>(
    data: [&[u8]; N],
    out: [&mut [u8]; N],
) {
    let mut s = KeccakState::<N, T>::new();
    for i in 0..data[0].len() / RATE {
        absorb_block::<N, T, RATE>(&mut s, T::slice_n(data, i * RATE, RATE));
    }
    let rem = data[0].len() % RATE;
    absorb_final::<N, T, RATE, DELIM>(&mut s, T::slice_n(data, data[0].len() - rem, rem).into());

    let outlen = out[0].len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    if blocks == 0 {
        squeeze_first_and_last::<N, T, RATE>(&s, out)
    } else {
        let (o0, mut o1) = T::split_at_mut_n(out, RATE);
        squeeze_first_block::<N, T, RATE>(&s, o0);
        for _i in 1..blocks {
            let (o, orest) = T::split_at_mut_n(o1, RATE);
            squeeze_next_block::<N, T, RATE>(&mut s, o);
            o1 = orest;
        }
        if last < outlen {
            squeeze_last::<N, T, RATE>(s, o1)
        }
    }
}
