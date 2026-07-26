use super::*;

use libcrux_intrinsics::avx2::Vec256;

#[cfg(hax)]
use crate::proof_utils::valid_rate;
#[cfg(hax)]
use hax_lib::int::ToInt;

// TRUSTED length-preservation post (this module is verification-deferred, see
// "Deferred SIMD store_block proofs" in proofs/verification_status.md):
// out0..out3 are `&mut [u8]` and Rust slice writes cannot change a slice's
// length on any path; the campaign proved this post (plus full functional
// correctness) for the structured predecessor of this code. Callers need it
// to re-type returned outputs back to fixed-size arrays.
#[hax_lib::ensures(|_| future(out0).len() == out0.len()
    && future(out1).len() == out1.len()
    && future(out2).len() == out2.len()
    && future(out3).len() == out3.len())]
#[inline(always)]
pub(crate) fn keccak4<const RATE: usize, const DELIM: u8>(
    data: &[&[u8]; 4],
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    #[cfg(not(eurydice))]
    debug_assert!(out0.len() == out1.len() && out0.len() == out2.len() && out0.len() == out3.len());
    #[cfg(not(eurydice))]
    debug_assert!(
        data[0].len() == data[1].len()
            && data[0].len() == data[2].len()
            && data[0].len() == data[3].len()
    );

    let mut s = KeccakState::<4, Vec256>::new();
    let data_len = data[0].len();
    for i in 0..data_len / RATE {
        s.absorb_block::<RATE>(data, i * RATE);
    }
    let rem = data_len % RATE;
    s.absorb_final::<RATE, DELIM>(data, data_len - rem, rem);

    let outlen = out0.len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    if blocks == 0 {
        s.squeeze4::<RATE>(out0, out1, out2, out3, 0, outlen);
    } else {
        s.squeeze4::<RATE>(out0, out1, out2, out3, 0, RATE);
        for i in 1..blocks {
            s.keccakf1600();
            s.squeeze4::<RATE>(out0, out1, out2, out3, i * RATE, RATE);
        }
        if last < outlen {
            s.keccakf1600();
            s.squeeze4::<RATE>(out0, out1, out2, out3, last, outlen - last);
        }
    }
}

// The requires/ensures below are the campaign's length contracts, restated on
// main's identical method bodies. This module is verification-deferred (see
// "Deferred SIMD store_block proofs" in proofs/verification_status.md), so the
// ensures are TRUSTED posts: pure slice-length preservation, which Rust slice
// writes guarantee on every path; the campaign proved them for this same code.
#[hax_lib::attributes]
impl KeccakState<4, Vec256> {
    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        start.to_int() + RATE.to_int() <= out0.len().to_int() &&
        out0.len() == out1.len() &&
        out0.len() == out2.len() &&
        out0.len() == out3.len()
    )]
    #[hax_lib::ensures(|_|
        future(out0).len() == out0.len() &&
        future(out1).len() == out1.len() &&
        future(out2).len() == out2.len() &&
        future(out3).len() == out3.len()
    )]
    pub(crate) fn squeeze_next_block<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
        start: usize,
    ) {
        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, start, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        RATE <= out0.len() &&
        out0.len() == out1.len() &&
        out0.len() == out2.len() &&
        out0.len() == out3.len()
    )]
    #[hax_lib::ensures(|_|
        future(out0).len() == out0.len() &&
        future(out1).len() == out1.len() &&
        future(out2).len() == out2.len() &&
        future(out3).len() == out3.len()
    )]
    pub(crate) fn squeeze_first_block<const RATE: usize>(
        &self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
    ) {
        self.squeeze4::<RATE>(out0, out1, out2, out3, 0, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        3 * RATE <= out0.len() &&
        out0.len() == out1.len() &&
        out0.len() == out2.len() &&
        out0.len() == out3.len()
    )]
    #[hax_lib::ensures(|_|
        future(out0).len() == out0.len() &&
        future(out1).len() == out1.len() &&
        future(out2).len() == out2.len() &&
        future(out3).len() == out3.len()
    )]
    pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
    ) {
        self.squeeze4::<RATE>(out0, out1, out2, out3, 0, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, RATE, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, 2 * RATE, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        5 * RATE <= out0.len() &&
        out0.len() == out1.len() &&
        out0.len() == out2.len() &&
        out0.len() == out3.len()
    )]
    #[hax_lib::ensures(|_|
        future(out0).len() == out0.len() &&
        future(out1).len() == out1.len() &&
        future(out2).len() == out2.len() &&
        future(out3).len() == out3.len()
    )]
    pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
    ) {
        self.squeeze4::<RATE>(out0, out1, out2, out3, 0, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, RATE, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, 2 * RATE, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, 3 * RATE, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, 4 * RATE, RATE);
    }
}
