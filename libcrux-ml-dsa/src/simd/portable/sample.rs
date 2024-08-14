use crate::constants::FIELD_MODULUS;

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

#[inline(always)]
pub fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;

    for byte in randomness {
        let try_0 = byte & 0xF;
        let try_1 = byte >> 4;

        if try_0 < 15 {
            let try_0 = try_0 as i32;

            // (try_0 * 26) >> 7 computes ⌊try_0 / 5⌋
            let try_0_mod_5 = try_0 - ((try_0 * 26) >> 7) * 5;

            out[sampled] = 2 - try_0_mod_5;

            sampled += 1;
        }

        if try_1 < 15 {
            let try_1 = try_1 as i32;
            let try_1_mod_5 = try_1 - ((try_1 * 26) >> 7) * 5;

            out[sampled] = 2 - try_1_mod_5;

            sampled += 1;
        }
    }

    sampled
}

#[inline(always)]
pub fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;

    for byte in randomness {
        let try_0 = byte & 0xF;
        let try_1 = byte >> 4;

        if try_0 < 9 {
            out[sampled] = 4 - (try_0 as i32);
            sampled += 1;
        }

        if try_1 < 9 {
            out[sampled] = 4 - (try_1 as i32);
            sampled += 1;
        }
    }

    sampled
}
