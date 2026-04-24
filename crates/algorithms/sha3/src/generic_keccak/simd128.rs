use super::*;

#[cfg(hax)]
use crate::proof_utils::{lemma_mul_succ_le, valid_rate};

use libcrux_intrinsics::arm64::_uint64x2_t;

/// Absorb phase of `keccak2`: initialise a two-lane Keccak state,
/// absorb all full rate-byte blocks of `data[0]` and `data[1]` in
/// parallel, then pad and absorb each lane's final partial block
/// with domain-separation byte `DELIM` and the pad10*1 terminator.
#[inline]
#[hax_lib::requires(valid_rate(RATE) && data[0].len() == data[1].len())]
#[hax_lib::fstar::options("--z3rlimit 300")]
pub(crate) fn absorb2<const RATE: usize, const DELIM: u8>(
    data: &[&[u8]; 2],
) -> KeccakState<2, _uint64x2_t> {
    let mut s = KeccakState::<2, _uint64x2_t>::new();
    let data_len = data[0].len();
    let data_blocks = data_len / RATE;
    for i in 0..data_blocks {
        #[cfg(hax)]
        lemma_mul_succ_le(i, data_blocks, RATE);

        s.absorb_block::<RATE>(data, i * RATE);
    }
    let rem = data_len % RATE;
    s.absorb_final::<RATE, DELIM>(data, data_len - rem, rem);
    s
}

/// Squeeze phase of `keccak2`: extract `out0.len()` bytes from each
/// lane of `s` into `out0` and `out1`, applying Keccak-f between
/// each full rate-byte block of output.
#[inline]
#[hax_lib::requires(valid_rate(RATE) && out0.len() == out1.len())]
#[hax_lib::ensures(|_| future(out0).len() == out0.len() && future(out1).len() == out1.len())]
#[hax_lib::fstar::options("--z3rlimit 300")]
pub(crate) fn squeeze2<const RATE: usize>(
    mut s: KeccakState<2, _uint64x2_t>,
    out0: &mut [u8],
    out1: &mut [u8],
) {
    #[cfg(hax)]
    let out0_len = out0.len();
    #[cfg(hax)]
    let out1_len = out1.len();

    let outlen = out0.len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    if blocks == 0 {
        s.squeeze2::<RATE>(out0, out1, 0, outlen);
    } else {
        s.squeeze2::<RATE>(out0, out1, 0, RATE);
        for i in 1..blocks {
            hax_lib::loop_invariant!(|_: usize| out0.len() == out0_len && out1.len() == out1_len);
            #[cfg(hax)]
            lemma_mul_succ_le(i, blocks, RATE);

            s.keccakf1600();
            s.squeeze2::<RATE>(out0, out1, i * RATE, RATE);
        }
        if last < outlen {
            s.keccakf1600();
            s.squeeze2::<RATE>(out0, out1, last, outlen - last);
        }
    }
}

#[inline]
#[hax_lib::requires(
    valid_rate(RATE) &&
    out0.len() == out1.len() &&
    data[0].len() == data[1].len()
)]
#[hax_lib::ensures(|_| future(out0).len() == out0.len() && future(out1).len() == out1.len())]
pub(crate) fn keccak2<const RATE: usize, const DELIM: u8>(
    data: &[&[u8]; 2],
    out0: &mut [u8],
    out1: &mut [u8],
) {
    #[cfg(not(eurydice))]
    debug_assert!(out0.len() == out1.len());
    #[cfg(not(eurydice))]
    debug_assert!(data[0].len() == data[1].len());

    let s = absorb2::<RATE, DELIM>(data);
    squeeze2::<RATE>(s, out0, out1);
}

#[hax_lib::attributes]
impl KeccakState<2, _uint64x2_t> {
    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        start.to_int() + RATE.to_int() <= out0.len().to_int() &&
        out0.len() == out1.len()
    )]
    #[hax_lib::ensures(|_| future(out0).len() == out0.len() && future(out1).len() == out1.len())]
    pub(crate) fn squeeze_next_block<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
        start: usize,
    ) {
        self.keccakf1600();
        self.squeeze2::<RATE>(out0, out1, start, RATE);
    }

    /// Write out the first block of Keccak output.
    ///
    /// This function MUST NOT be called after any of the other `squeeze_*`
    /// functions have been called, since that would result in a duplicate output
    /// block.
    #[hax_lib::requires(
        valid_rate(RATE) &&
        RATE <= out0.len() &&
        out0.len() == out1.len()
    )]
    #[hax_lib::ensures(|_| future(out0).len() == out0.len() && future(out1).len() == out1.len())]
    pub(crate) fn squeeze_first_block<const RATE: usize>(&self, out0: &mut [u8], out1: &mut [u8]) {
        self.squeeze2::<RATE>(out0, out1, 0, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        3 * RATE <= out0.len() &&
        out0.len() == out1.len()
    )]
    #[hax_lib::ensures(|_| future(out0).len() == out0.len() && future(out1).len() == out1.len())]
    pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
    ) {
        self.squeeze2::<RATE>(out0, out1, 0, RATE);

        self.keccakf1600();
        self.squeeze2::<RATE>(out0, out1, RATE, RATE);

        self.keccakf1600();
        self.squeeze2::<RATE>(out0, out1, 2 * RATE, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        5 * RATE <= out0.len() &&
        out0.len() == out1.len()
    )]
    #[hax_lib::ensures(|_| future(out0).len() == out0.len() && future(out1).len() == out1.len())]
    pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
    ) {
        self.squeeze2::<RATE>(out0, out1, 0, RATE);

        self.keccakf1600();
        self.squeeze2::<RATE>(out0, out1, RATE, RATE);

        self.keccakf1600();
        self.squeeze2::<RATE>(out0, out1, 2 * RATE, RATE);

        self.keccakf1600();
        self.squeeze2::<RATE>(out0, out1, 3 * RATE, RATE);

        self.keccakf1600();
        self.squeeze2::<RATE>(out0, out1, 4 * RATE, RATE);
    }
}
