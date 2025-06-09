use super::*;

impl KeccakState<1, u64> {
    #[inline(always)]
    pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(&mut self, out: &mut [u8]) {
        self.squeeze1::<RATE>(out, 0, RATE);

        keccakf1600(self);
        self.squeeze1::<RATE>(out, RATE, RATE);

        keccakf1600(self);
        self.squeeze1::<RATE>(out, 2 * RATE, RATE);
    }

    #[inline(always)]
    pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(&mut self, out: &mut [u8]) {
        self.squeeze1::<RATE>(out, 0, RATE);

        keccakf1600(self);
        self.squeeze1::<RATE>(out, RATE, RATE);

        keccakf1600(self);
        self.squeeze1::<RATE>(out, 2 * RATE, RATE);

        keccakf1600(self);
        self.squeeze1::<RATE>(out, 3 * RATE, RATE);

        keccakf1600(self);
        self.squeeze1::<RATE>(out, 4 * RATE, RATE);
    }
}

#[cfg(feature = "simd128")]
impl KeccakState<2, libcrux_intrinsics::arm64::_uint64x2_t> {
    #[inline(always)]
    pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
    ) {
        self.squeeze2::<RATE>(out0, out1, 0, RATE);

        keccakf1600(self);
        self.squeeze2::<RATE>(out0, out1, RATE, RATE);

        keccakf1600(self);
        self.squeeze2::<RATE>(out0, out1, 2 * RATE, RATE);
    }

    #[inline(always)]
    pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
    ) {
        self.squeeze2::<RATE>(out0, out1, 0, RATE);

        keccakf1600(self);
        self.squeeze2::<RATE>(out0, out1, RATE, RATE);

        keccakf1600(self);
        self.squeeze2::<RATE>(out0, out1, 2 * RATE, RATE);

        keccakf1600(self);
        self.squeeze2::<RATE>(out0, out1, 3 * RATE, RATE);

        keccakf1600(self);
        self.squeeze2::<RATE>(out0, out1, 4 * RATE, RATE);
    }
}
