use crate::{constants::FIELD_MODULUS, helper::cloop};

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"(Seq.length $randomness) / 3 <= Seq.length $out"#))]
#[hax_lib::ensures(|result| fstar!(r#"let s = Spec.MLDSA.Math.rejection_sample_field_modulus $randomness in
    v $result <= Seq.length ${out}_future /\ v $result == Seq.length s /\
    Seq.slice ${out}_future 0 (v $result) == s"#))]
pub fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;

    cloop! {
        for bytes in randomness.chunks_exact(3) {
            let b0 = bytes[0] as i32;
            let b1 = bytes[1] as i32;
            let b2 = bytes[2] as i32;

            let coefficient = ((b2 << 16) | (b1 << 8) | b0) & 0x00_7F_FF_FF;

            if coefficient < FIELD_MODULUS {
                out[sampled] = coefficient;
                sampled += 1;
            }
        }
    }

    sampled
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"(Seq.length $randomness) * 2 <= Seq.length $out"#))]
#[hax_lib::ensures(|result| fstar!(r#"let s = Spec.MLDSA.Math.rejection_sample_eta_2 $randomness in
    v $result <= Seq.length ${out}_future /\ v $result == Seq.length s /\
    Seq.slice ${out}_future 0 (v $result) == s"#))]
pub fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;

    cloop! {
        for byte in randomness.iter() {
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
    }

    sampled
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"(Seq.length $randomness) * 2 <= Seq.length $out"#))]
#[hax_lib::ensures(|result| fstar!(r#"let s = Spec.MLDSA.Math.rejection_sample_eta_4 $randomness in
    v $result <= Seq.length ${out}_future /\ v $result == Seq.length s /\
    Seq.slice ${out}_future 0 (v $result) == s"#))]
pub fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;

    cloop! {
        for byte in randomness.iter() {
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
    }

    sampled
}
