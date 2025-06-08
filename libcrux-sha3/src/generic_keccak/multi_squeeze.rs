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
