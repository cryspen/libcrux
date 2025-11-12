use super::*;

#[cfg(hax)]
#[hax_lib::fstar::replace("open Libcrux_sha3.Lemmas")]
const _: () = ();

#[hax_lib::attributes]
impl KeccakState<1, u64> {
    #[inline(always)]
    #[hax_lib::requires(
        RATE <= 200 &&
        start.to_int() + RATE.to_int() <= out.len().to_int()
    )]
    #[hax_lib::ensures(
        |_| future(out).len() == out.len()
    )]
    pub(crate) fn squeeze_next_block<const RATE: usize>(&mut self, out: &mut [u8], start: usize) {
        self.keccakf1600();
        self.squeeze::<RATE>(out, start, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        RATE <= 200 &&
        RATE <= out.len()
    )]
    #[hax_lib::ensures(
        |_| future(out).len() == out.len()
    )]
    pub(crate) fn squeeze_first_block<const RATE: usize>(&self, out: &mut [u8]) {
        self.squeeze::<RATE>(out, 0, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        RATE <= 200 &&
        3 * RATE <= out.len()
    )]
    #[hax_lib::ensures(
        |_| future(out).len() == out.len()
    )]
    pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(&mut self, out: &mut [u8]) {
        self.squeeze::<RATE>(out, 0, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, RATE, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, 2 * RATE, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        RATE <= 200 &&
        5 * RATE <= out.len()
    )]
    #[hax_lib::ensures(
        |_| future(out).len() == out.len()
    )]
    pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(&mut self, out: &mut [u8]) {
        self.squeeze::<RATE>(out, 0, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, RATE, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, 2 * RATE, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, 3 * RATE, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, 4 * RATE, RATE);
    }
}

#[hax_lib::requires(
    RATE != 0 &&
    RATE <= 200 &&
    RATE % 8 == 0
)]
#[hax_lib::ensures(|_|
    future(out).len() == out.len())
]
#[hax_lib::fstar::options("--split_queries always --query_stats --z3rlimit 300")]
#[inline]
pub(crate) fn keccak1<const RATE: usize, const DELIM: u8>(data: &[u8], out: &mut [u8]) {
    let mut s = KeccakState::<1, u64>::new();
    let data_len = data.len();
    for i in 0..data_len / RATE {
        hax_lib::fstar!("mul_succ_le (v i) (v (data_len /! v_RATE)) (v v_RATE)");

        s.absorb_block::<RATE>(&[data], i * RATE);
    }
    let rem = data_len % RATE;
    s.absorb_final::<RATE, DELIM>(&[data], data_len - rem, rem);

    let outlen = out.len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    if blocks == 0 {
        s.squeeze::<RATE>(out, 0, outlen);
    } else {
        s.squeeze::<RATE>(out, 0, RATE);
        for i in 1..blocks {
            hax_lib::loop_invariant!(|_: usize| out.len() == outlen);
            hax_lib::fstar!("mul_succ_le (v i) (v blocks) (v v_RATE)");

            s.keccakf1600();
            s.squeeze::<RATE>(out, i * RATE, RATE);
        }
        if last < outlen {
            s.keccakf1600();
            s.squeeze::<RATE>(out, last, outlen - last);
        }
    }
}
