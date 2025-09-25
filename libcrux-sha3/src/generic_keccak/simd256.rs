use super::*;

use libcrux_intrinsics::avx2::Vec256;

#[hax_lib::attributes]
impl KeccakState<4, Vec256> {
    #[hax_lib::requires(
        RATE <= 200 &&
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
    #[inline(always)]
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

    #[hax_lib::requires(
        RATE <= 200 &&
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
    #[inline(always)]
    pub(crate) fn squeeze_first_block<const RATE: usize>(
        &self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
    ) {
        self.squeeze4::<RATE>(out0, out1, out2, out3, 0, RATE);
    }

    #[hax_lib::requires(
        RATE <= 200 &&
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
    #[inline(always)]
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

    #[hax_lib::requires(
        RATE <= 200 &&
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
    #[inline(always)]
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

#[hax_lib::fstar::before(
    r#"
let rec mul_succ_le (k n d: nat)
  : Lemma
    (requires k < n && d > 0)
    (ensures k * d + d <= n * d)
    (decreases n) =
  if n = 0 then ()
  else if k = n - 1 then ()
  else mul_succ_le k (n - 1) d
"#
)]
#[hax_lib::requires(
    RATE != 0 &&
    RATE <= 200 &&
    RATE % 8 == 0 &&
    (RATE % 32 == 8 || RATE % 32 == 16) &&
    data[0].len() == data[1].len() &&
    data[0].len() == data[2].len() &&
    data[0].len() == data[3].len() &&
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
#[hax_lib::fstar::options("--split_queries always --z3rlimit 300")]
#[inline]
pub(crate) fn keccak4<const RATE: usize, const DELIM: u8>(
    data: &[&[u8]; 4],
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    debug_assert!(
        data[0].len() == data[1].len()
            && data[0].len() == data[2].len()
            && data[0].len() == data[3].len()
    );
    debug_assert!(out0.len() == out1.len() && out0.len() == out2.len() && out0.len() == out3.len());

    let mut s = KeccakState::<4, Vec256>::new();
    let data_len = data[0].len();
    for i in 0..data_len / RATE {
        hax_lib::fstar!("mul_succ_le (v i) (v (data_len /! v_RATE)) (v v_RATE)");
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
            hax_lib::loop_invariant!(|_: usize| out0.len() == outlen
                && out0.len() == out1.len()
                && out0.len() == out2.len()
                && out0.len() == out3.len());
            hax_lib::fstar!("mul_succ_le (v i) (v blocks) (v v_RATE)");
            s.keccakf1600();
            s.squeeze4::<RATE>(out0, out1, out2, out3, i * RATE, RATE);
        }
        if last < outlen {
            s.keccakf1600();
            s.squeeze4::<RATE>(out0, out1, out2, out3, last, outlen - last);
        }
    }
}
