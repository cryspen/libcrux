//! The generic SHA3 implementation that uses portable or platform specific
//! sub-routines.

use core::ops::Index;

use crate::traits::*;

#[cfg_attr(hax, hax_lib::opaque_type)]
#[derive(Debug, Clone, Copy)]
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

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs.
#[cfg_attr(hax, hax_lib::opaque_type)]
#[derive(Clone, Copy)]
pub(crate) struct KeccakXofState<
    const PARALLEL_LANES: usize,
    const BLOCK_SIZE: usize,
    STATE: KeccakStateItem<PARALLEL_LANES>,
> {
    inner: KeccakState<PARALLEL_LANES, STATE>,

    // Buffer inputs on absorb.
    buf: [[u8; BLOCK_SIZE]; PARALLEL_LANES],

    // Buffered length.
    buf_len: usize,

    // Needs sponge.
    sponge: bool,
}

impl<
        const PARALLEL_LANES: usize,
        const BLOCK_SIZE: usize,
        STATE: KeccakStateItem<PARALLEL_LANES>,
    > KeccakXofState<PARALLEL_LANES, BLOCK_SIZE, STATE>
{
    /// An all zero block
    pub(crate) const fn zero_block() -> [u8; BLOCK_SIZE] {
        [0u8; BLOCK_SIZE]
    }

    /// Generate a new keccak xof state.
    pub(crate) fn new() -> Self {
        Self {
            inner: KeccakState::new(),
            buf: [Self::zero_block(); PARALLEL_LANES],
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
    pub(crate) fn absorb(&mut self, inputs: [&[u8]; PARALLEL_LANES]) {
        // eprintln!("absorb ...");
        // eprintln!("state before absorb (xof)");
        // for s in self.inner.st {
        //     println!(
        //         " {} {} {} {} {}",
        //         STATE::print(&s[0]),
        //         STATE::print(&s[1]),
        //         STATE::print(&s[2]),
        //         STATE::print(&s[3]),
        //         STATE::print(&s[4])
        //     );
        // }

        let remainder = self.absorb_full(inputs);

        // eprintln!("remainder: {remainder}");
        // ... buffer the rest if there's not enough input (left).
        if remainder > 0 {
            debug_assert!(
                self.buf_len == 0  // We consumed everything (or it was empty all along).
                 || self.buf_len + remainder <= BLOCK_SIZE
            );
            // eprintln!("buffering: {} bytes", remainder);

            let input_len = inputs[0].len();
            for i in 0..PARALLEL_LANES {
                self.buf[i][self.buf_len..self.buf_len + remainder]
                    .copy_from_slice(&inputs[i][input_len - remainder..]);
            }
            self.buf_len += remainder;
        }
        // eprintln!("state after absorb (xof)");
        // for s in self.inner.st {
        //     eprintln!(
        //         " {} {} {} {} {}",
        //         STATE::print(&s[0]),
        //         STATE::print(&s[1]),
        //         STATE::print(&s[2]),
        //         STATE::print(&s[3]),
        //         STATE::print(&s[4])
        //     );
        // }
    }

    fn absorb_full(&mut self, inputs: [&[u8]; PARALLEL_LANES]) -> usize {
        debug_assert!(PARALLEL_LANES > 0);
        debug_assert!(self.buf_len < BLOCK_SIZE);
        #[cfg(debug_assertions)]
        {
            for block in inputs {
                debug_assert!(block.len() == inputs[0].len());
            }
        }

        // Check if there are buffered bytes to absorb first and consume them.
        let input_consumed = self.fill_buffer(inputs);
        // eprintln!("consumed: {input_consumed}");
        // eprintln!("need to consume: {}", inputs[0].len() / BLOCK_SIZE);

        if input_consumed > 0 {
            // We have a full block in the local buffer now.
            let borrowed: [&[u8]; PARALLEL_LANES] =
                core::array::from_fn(|i| &self.buf[i] as &[u8]);
            STATE::load_block::<BLOCK_SIZE>(&mut self.inner.st, borrowed);
            keccakf1600(&mut self.inner);

            // "empty" the local buffer
            self.buf_len = 0;
        }

        // We only need to consume the rest of the input.
        let input_to_consume = inputs[0].len() - input_consumed;

        // Consume the (rest of the) input ...
        let num_blocks = input_to_consume / BLOCK_SIZE;
        let remainder = input_to_consume % BLOCK_SIZE;
        for i in 0..num_blocks {
            // We only get in here if `input_len / RATE > 0`.
            STATE::load_block::<BLOCK_SIZE>(
                &mut self.inner.st,
                STATE::slice_n(inputs, input_consumed + i * BLOCK_SIZE, BLOCK_SIZE),
            );
            keccakf1600(&mut self.inner);
        }

        remainder
    }

    /// Consume the internal buffer and the required amount of the input to pad to
    /// `BLOCK_SIZE`.
    ///
    /// Returns the `consumed` bytes from `inputs` if there's enough buffered
    /// content to consume, and `0` otherwise.
    /// If `consumed > 0` is returned, `self.buf` contains a full block to be
    /// loaded.
    fn fill_buffer(&mut self, inputs: [&[u8]; PARALLEL_LANES]) -> usize {
        // eprintln!("fill_buffer");
        let input_len = inputs[0].len();
        let mut consumed = 0;
        if self.buf_len > 0 {
            // There's something buffered internally to consume.
            if self.buf_len + input_len >= BLOCK_SIZE {
                // We have enough data when combining the internal buffer and
                // the input.
                consumed = BLOCK_SIZE - self.buf_len;
                for i in 0..PARALLEL_LANES {
                    self.buf[i][self.buf_len..].copy_from_slice(&inputs[i][..consumed]);
                }
                self.buf_len += consumed;
            }
        }
        consumed
    }

    /// Absorb a final block.
    ///
    /// The `inputs` block may be empty. Everything in the `inputs` block beyond
    /// `RATE` bytes is ignored.
    #[inline(always)]
    pub(crate) fn absorb_final<const DELIMITER: u8>(&mut self, inputs: [&[u8]; PARALLEL_LANES]) {
        let remainder = self.absorb_full(inputs);

        // // Consume the remaining bytes.
        // if remainder > 0 {
        //     debug_assert!(
        //         self.buf_len == 0  // We consumed everything (or it was empty all along).
        //          || self.buf_len + remainder <= BLOCK_SIZE
        //     );
        //     eprintln!("buffering: {} bytes", remainder);
        // }

        // Consume the remaining bytes.
        // This may be in the local buffer or in the input.
        let input_len = inputs[0].len();
        let mut blocks = [[0u8; 200]; PARALLEL_LANES];
        // eprintln!("local buf: ({}) {:x?}", self.buf_len, self.buf);
        for i in 0..PARALLEL_LANES {
            if self.buf_len > 0 {
                blocks[i][0..self.buf_len].copy_from_slice(&self.buf[i][0..self.buf_len]);
            }
            if remainder > 0 {
                blocks[i][self.buf_len..self.buf_len + remainder]
                    .copy_from_slice(&inputs[i][input_len - remainder..]);
            }
            blocks[i][self.buf_len + remainder] = DELIMITER;
            blocks[i][BLOCK_SIZE - 1] |= 0x80;
        }
        // eprintln!("loading: {blocks:x?}");
        STATE::load_block_full::<BLOCK_SIZE>(&mut self.inner.st, blocks);
        keccakf1600(&mut self.inner);

        // println!("state after absorb final (xof)");
        // for s in self.inner.st {
        //     println!(
        //         " {} {} {} {} {}",
        //         STATE::print(&s[0]),
        //         STATE::print(&s[1]),
        //         STATE::print(&s[2]),
        //         STATE::print(&s[3]),
        //         STATE::print(&s[4])
        //     );
        // }
    }

    /// Squeeze `N` x `LEN` bytes.
    #[inline(always)]
    pub(crate) fn squeeze(&mut self, out: [&mut [u8]; PARALLEL_LANES]) {
        // println!("state before squeeze (xof)");
        // for s in self.inner.st {
        //     println!(
        //         " {} {} {} {} {}",
        //         STATE::print(&s[0]),
        //         STATE::print(&s[1]),
        //         STATE::print(&s[2]),
        //         STATE::print(&s[3]),
        //         STATE::print(&s[4])
        //     );
        // }
        if self.sponge {
            // If we called `squeeze` before, call f1600 first.
            // We do it this way around so that we don't call f1600 at the end
            // when we don't need it.
            keccakf1600(&mut self.inner);
        }

        // How many blocks do we need to squeeze out?
        let out_len = out[0].len();
        let blocks = out_len / BLOCK_SIZE;
        let last = out_len - (out_len % BLOCK_SIZE);

        // Squeeze out one to start with.
        let (out0, mut out_rest) = STATE::split_at_mut_n(out, BLOCK_SIZE.min(out_len));
        STATE::store::<BLOCK_SIZE>(&self.inner.st, out0);

        // If we got asked for more than one block, squeeze out more.
        for _ in 1..blocks {
            // Here we know that we always have full blocks to write out.
            let (out0, tmp) = STATE::split_at_mut_n(out_rest, BLOCK_SIZE);
            keccakf1600(&mut self.inner);
            STATE::store::<BLOCK_SIZE>(&self.inner.st, out0);
            out_rest = tmp;
        }

        if last < out_len {
            // Squeeze out the last partial block
            keccakf1600(&mut self.inner);
            STATE::store::<BLOCK_SIZE>(&self.inner.st, out_rest);
        }

        self.sponge = true;
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
    last: [&[u8]; N],
) {
    debug_assert!(N > 0 && last[0].len() < RATE);
    let last_len = last[0].len();
    let mut blocks = [[0u8; 200]; N];
    for i in 0..N {
        if last_len > 0 {
            blocks[i][0..last_len].copy_from_slice(last[i]);
        }
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
    absorb_final::<N, T, RATE, DELIM>(&mut s, T::slice_n(data, data[0].len() - rem, rem));

    let outlen = out[0].len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    // println!("state before squeeze");
    // for s in s.st {
    //     println!(
    //         " {} {} {} {} {}",
    //         T::print(&s[0]),
    //         T::print(&s[1]),
    //         T::print(&s[2]),
    //         T::print(&s[3]),
    //         T::print(&s[4])
    //     );
    // }

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

#[inline(always)]
pub(crate) fn keccak_xof<
    const PARALLEL_LANES: usize,
    STATE: KeccakStateItem<PARALLEL_LANES>,
    const BLOCK_SIZE: usize,
    const DELIMITER: u8,
>(
    data: [&[u8]; PARALLEL_LANES],
    out: [&mut [u8]; PARALLEL_LANES],
) {
    let mut state = KeccakXofState::<PARALLEL_LANES, BLOCK_SIZE, STATE>::new();
    state.absorb(data);
    state.absorb_final::<DELIMITER>([&[]; PARALLEL_LANES]);
    state.squeeze(out);
}
