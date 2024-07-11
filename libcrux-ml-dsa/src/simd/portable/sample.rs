use crate::simd::traits::FIELD_MODULUS;

#[inline(always)]
pub fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;

    for bytes in randomness.chunks(3) {
        let b0 = bytes[0] as i32;
        let b1 = bytes[1] as i32;
        let b2 = bytes[2] as i32;

        let coefficient = ((b2 << 16) | (b1 << 8) | b0) & 0x00_7F_FF_FF;

        if coefficient < FIELD_MODULUS {
            out[sampled] = coefficient;
            sampled += 1;
        }
    }

    sampled
}
