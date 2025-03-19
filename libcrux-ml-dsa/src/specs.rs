use hax_lib::*;

#[fstar::replace_body(r#"Seq.length randomness / 3 <= Lib.IntTypes.max_size_t /\
    Seq.length $randomness / 3 <= Seq.length $out"#)]
pub(crate) fn rejection_sample_less_than_field_modulus_pre(randomness: &[u8], out: &[i32]) -> Prop {
    true.into()
}

#[fstar::replace_body(r#"let s = Spec.MLDSA.Math.rejection_sample_field_modulus $randomness in
    v $r <= Seq.length out /\ v $r == Seq.length s /\
    Seq.slice out 0 (v $r) == s"#)]
pub(crate) fn rejection_sample_less_than_field_modulus_post(randomness: &[u8], out: &[i32], r: usize) -> Prop {
    true.into()
}

#[fstar::replace_body(r#"Seq.length randomness * 2 <= Lib.IntTypes.max_size_t /\
    Seq.length $randomness * 2 <= Seq.length $out"#)]
pub(crate) fn rejection_sample_less_than_eta_equals_2_pre(randomness: &[u8], out: &[i32]) -> Prop {
    true.into()
}

#[fstar::replace_body(r#"let s = Spec.MLDSA.Math.rejection_sample_eta_2 $randomness in
    v $r <= Seq.length out /\ v $r == Seq.length s /\
    Seq.slice out 0 (v $r) == s"#)]
pub(crate) fn rejection_sample_less_than_eta_equals_2_post(randomness: &[u8], out: &[i32], r: usize) -> Prop {
    true.into()
}

#[fstar::replace_body(r#"Seq.length randomness * 2 <= Lib.IntTypes.max_size_t /\
    Seq.length $randomness * 2 <= Seq.length $out"#)]
pub(crate) fn rejection_sample_less_than_eta_equals_4_pre(randomness: &[u8], out: &[i32]) -> Prop {
    true.into()
}

#[fstar::replace_body(r#"let s = Spec.MLDSA.Math.rejection_sample_eta_4 $randomness in
    v $r <= Seq.length out /\ v $r == Seq.length s /\
    Seq.slice out 0 (v $r) == s"#)]
pub(crate) fn rejection_sample_less_than_eta_equals_4_post(randomness: &[u8], out: &[i32], r: usize) -> Prop {
    true.into()
}
