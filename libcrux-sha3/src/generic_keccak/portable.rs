use super::*;

#[hax_lib::attributes]
impl KeccakState<1, u64> {
    #[inline(always)]
    #[hax_lib::requires(
        RATE % 8 == 0 &&
        RATE < 192 &&
        RATE <= out.len() &&
        start <= out.len() &&
        start <= out.len() - RATE &&
        start + RATE <= out.len()
    )]
    pub(crate) fn squeeze_next_block<const RATE: usize>(&mut self, out: &mut [u8], start: usize) {
        self.keccakf1600();
        self.squeeze::<RATE>(out, start, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        RATE % 8 == 0 &&
        RATE < 192 &&
        RATE <= out.len()
    )]
    pub(crate) fn squeeze_first_block<const RATE: usize>(&self, out: &mut [u8]) {
        self.squeeze::<RATE>(out, 0, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        RATE % 8 == 0 &&
        RATE < 192 &&
        3 * RATE <= out.len()
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
        RATE % 8 == 0 &&
        RATE < 192 &&
        5 * RATE <= out.len()
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

#[inline]
// #[hax_lib::requires(
//     RATE % 8 == 0 &&
//     RATE != 0 &&
//     RATE < 192 &&
//     data.len() + RATE <= usize::MAX
// )]
// #[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn keccak1<const RATE: usize, const DELIM: u8>(data: &[u8], out: &mut [u8]) {
    let mut s = KeccakState::<1, u64>::new();
    let data_len = data.len();
    for i in 0..data_len / RATE {
        hax_lib::loop_invariant!(|i: usize| {
            data.len() == data_len && (i * RATE) + RATE <= data_len
        });
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
            s.keccakf1600();
            s.squeeze::<RATE>(out, i * RATE, RATE);
        }
        if last < outlen {
            s.keccakf1600();
            s.squeeze::<RATE>(out, last, outlen - last);
        }
    }
}
