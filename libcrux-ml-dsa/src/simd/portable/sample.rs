use crate::constants::FIELD_MODULUS;

#[inline(always)]
#[hax_lib::requires(fstar!(r#"Seq.length randomness / 3 <= Lib.IntTypes.max_size_t /\
    Seq.length $randomness / 3 <= Seq.length $out"#))]
#[hax_lib::ensures(|result| fstar!(r#"let s = Spec.MLDSA.Math.rejection_sample_field_modulus $randomness in
    v $result <= Seq.length ${out}_future /\ v $result == Seq.length s /\
    Seq.slice ${out}_future 0 (v $result) == s"#))]
pub fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;
    let _out_len = out.len();
    hax_lib::fstar!(
        r#"Lib.LoopCombinators.eq_repeati0 0 (Spec.MLDSA.Math.rejection_sample_field_modulus_inner $randomness) Seq.empty"#
    );

    for i in 0..randomness.len() / 3 {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(r#"
              v $sampled <= v $i /\
              Seq.length $out == v $_out_len /\
              (let samples = Lib.LoopCombinators.repeati (v $i)
                (Spec.MLDSA.Math.rejection_sample_field_modulus_inner $randomness) Seq.empty in
              v $sampled == Seq.length samples /\
              Seq.slice $out 0 (Seq.length samples) == samples)"#
            )
        });
        let b0 = randomness[i * 3] as i32;
        let b1 = randomness[i * 3 + 1] as i32;
        let b2 = randomness[i * 3 + 2] as i32;

        let coefficient = ((b2 << 16) | (b1 << 8) | b0) & 0x00_7F_FF_FF;
        hax_lib::fstar!(
            r#"Spec.MLDSA.Math.rejection_sample_coefficient_lemma $randomness (v $i);
            Lib.LoopCombinators.unfold_repeati (v $i + 1) 
                (Spec.MLDSA.Math.rejection_sample_field_modulus_inner $randomness) Seq.empty (v $i)"#
        );

        if coefficient < FIELD_MODULUS {
            out[sampled] = coefficient;
            sampled += 1;
        }
        hax_lib::fstar!(
            r#"let samples = Lib.LoopCombinators.repeati (v $i + 1)
                (Spec.MLDSA.Math.rejection_sample_field_modulus_inner $randomness) Seq.empty in
            Lib.Sequence.eq_intro #i32 #(Seq.length samples) (Seq.slice $out 0 (Seq.length samples)) samples"#
        );
    }

    sampled
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 800 --ext context_pruning --z3refresh")]
#[hax_lib::requires(fstar!(r#"Seq.length randomness * 2 <= Lib.IntTypes.max_size_t /\
    Seq.length $randomness * 2 <= Seq.length $out"#))]
#[hax_lib::ensures(|result| fstar!(r#"let s = Spec.MLDSA.Math.rejection_sample_eta_2 $randomness in
    v $result <= Seq.length ${out}_future /\ v $result == Seq.length s /\
    Seq.slice ${out}_future 0 (v $result) == s"#))]
pub fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;
    let _out_len = out.len();
    hax_lib::fstar!(
        r#"Lib.LoopCombinators.eq_repeati0 0 (Spec.MLDSA.Math.rejection_sample_eta_2_inner $randomness) Seq.empty"#
    );

    for i in 0..randomness.len() {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(r#"
              v $i >= 0 /\ v $i <= Seq.length $randomness /\
              v $sampled <= v $i * 2 /\
              Seq.length $out == v $_out_len /\
              (let samples = Lib.LoopCombinators.repeati (v $i)
                (Spec.MLDSA.Math.rejection_sample_eta_2_inner $randomness) Seq.empty in
              v $sampled == Seq.length samples /\
              Seq.slice $out 0 (Seq.length samples) == samples)"#
            )
        });
        let byte = randomness[i];
        let try_0 = byte & 0xF;
        let try_1 = byte >> 4;
        hax_lib::fstar!(
            r#"Lib.LoopCombinators.unfold_repeati (v $i + 1) 
                (Spec.MLDSA.Math.rejection_sample_eta_2_inner $randomness) Seq.empty (v $i)"#
        );

        if try_0 < 15 {
            let try_0 = try_0 as i32;

            // (try_0 * 26) >> 7 computes ⌊try_0 / 5⌋
            let try_0_mod_5 = try_0 - ((try_0 * 26) >> 7) * 5;
            hax_lib::fstar!(
                r#"assert ($try_0_mod_5 == ($try_0 %! mk_i32 5));
                assert ((mk_i32 2 -. $try_0_mod_5) == (mk_i32 2 -! $try_0_mod_5))"#
            );

            out[sampled] = 2 - try_0_mod_5;

            sampled += 1;
        }

        if try_1 < 15 {
            let try_1 = try_1 as i32;
            let try_1_mod_5 = try_1 - ((try_1 * 26) >> 7) * 5;
            hax_lib::fstar!(
                r#"assert ($try_1_mod_5 == ($try_1 %! mk_i32 5));
                assert ((mk_i32 2 -. $try_1_mod_5) == (mk_i32 2 -! $try_1_mod_5))"#
            );

            out[sampled] = 2 - try_1_mod_5;

            sampled += 1;
        }
        hax_lib::fstar!(
            r#"let samples = Lib.LoopCombinators.repeati (v $i + 1)
                (Spec.MLDSA.Math.rejection_sample_eta_2_inner $randomness) Seq.empty in
            Lib.Sequence.eq_intro #i32 #(Seq.length samples) (Seq.slice $out 0 (Seq.length samples)) samples"#
        );
    }

    sampled
}

#[inline(always)]
#[hax_lib::fstar::options("--ext context_pruning --z3refresh")]
#[hax_lib::requires(fstar!(r#"Seq.length randomness * 2 <= Lib.IntTypes.max_size_t /\
    Seq.length $randomness * 2 <= Seq.length $out"#))]
#[hax_lib::ensures(|result| fstar!(r#"let s = Spec.MLDSA.Math.rejection_sample_eta_4 $randomness in
    v $result <= Seq.length ${out}_future /\ v $result == Seq.length s /\
    Seq.slice ${out}_future 0 (v $result) == s"#))]
pub fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;
    let _out_len = out.len();
    hax_lib::fstar!(
        r#"Lib.LoopCombinators.eq_repeati0 0 (Spec.MLDSA.Math.rejection_sample_eta_4_inner $randomness) Seq.empty"#
    );

    for i in 0..randomness.len() {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(r#"
              v $i >= 0 /\ v $i <= Seq.length $randomness /\
              v $sampled <= v $i * 2 /\
              Seq.length $out == v $_out_len /\
              (let samples = Lib.LoopCombinators.repeati (v $i)
                (Spec.MLDSA.Math.rejection_sample_eta_4_inner $randomness) Seq.empty in
              v $sampled == Seq.length samples /\
              Seq.slice $out 0 (Seq.length samples) == samples)"#
            )
        });
        let byte = randomness[i];
        let try_0 = byte & 0xF;
        let try_1 = byte >> 4;
        hax_lib::fstar!(
            r#"Lib.LoopCombinators.unfold_repeati (v $i + 1) 
                (Spec.MLDSA.Math.rejection_sample_eta_4_inner $randomness) Seq.empty (v $i)"#
        );

        if try_0 < 9 {
            out[sampled] = 4 - (try_0 as i32);
            sampled += 1;
        }

        if try_1 < 9 {
            out[sampled] = 4 - (try_1 as i32);
            sampled += 1;
        }
        hax_lib::fstar!(
            r#"let samples = Lib.LoopCombinators.repeati (v $i + 1)
                (Spec.MLDSA.Math.rejection_sample_eta_4_inner $randomness) Seq.empty in
            Lib.Sequence.eq_intro #i32 #(Seq.length samples) (Seq.slice $out 0 (Seq.length samples)) samples"#
        );
    }

    sampled
}
