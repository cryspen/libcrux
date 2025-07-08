use super::*;

impl KeccakState<1, u64> {
    #[inline(always)]
    pub(crate) fn squeeze_next_block<const RATE: usize>(
        &mut self,
        out: &mut [Secret<u8>],
        start: usize,
    ) {
        self.keccakf1600();
        self.squeeze::<RATE>(out, start, RATE);
    }

    #[inline(always)]
    pub(crate) fn squeeze_first_block<const RATE: usize>(&self, out: &mut [Secret<u8>]) {
        self.squeeze::<RATE>(out, 0, RATE);
    }

    #[inline(always)]
    pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(&mut self, out: &mut [Secret<u8>]) {
        self.squeeze::<RATE>(out, 0, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, RATE, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, 2 * RATE, RATE);
    }

    #[inline(always)]
    pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(&mut self, out: &mut [Secret<u8>]) {
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
pub(crate) fn keccak1<const RATE: usize, const DELIM: u8>(
    data: &[Secret<u8>],
    out: &mut [Secret<u8>],
) {
    let mut s = KeccakState::<1, u64>::new();
    let data_len = data.len();
    for i in 0..data_len / RATE {
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
