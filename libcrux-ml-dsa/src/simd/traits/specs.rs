use crate::constants::Gamma2;
use hax_lib::*;

pub(crate) const PRIME: u32 = 8380417;

pub(crate) const MONT_R: u32 = 8380417;

pub(crate) const FIELD_MAX: u32 = 8380416;

pub(crate) const FIELD_MID: u32 = 4190208;

pub(crate) const NTT_BASE_BOUND: u32 = FIELD_MID;

const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

type SIMDContent = [i32; COEFFICIENTS_IN_SIMD_UNIT];

pub(crate) fn int_is_i32(i: Int) -> bool {
    i <= i32::MAX.to_int() && i >= i32::MIN.to_int()
}

pub(crate) fn zero_post(result: &SIMDContent) -> bool {
    *result == [0i32; COEFFICIENTS_IN_SIMD_UNIT]
}

pub(crate) fn from_coefficient_array_pre(array: &[i32], out: &SIMDContent) -> bool {
    array.len() == COEFFICIENTS_IN_SIMD_UNIT
}

pub(crate) fn from_coefficient_array_post(
    array: &[i32],
    out: &SIMDContent,
    future_out: &SIMDContent,
) -> bool {
    future_out == array
}

pub(crate) fn to_coefficient_array_pre(value: &SIMDContent, out: &[i32]) -> bool {
    out.len() == COEFFICIENTS_IN_SIMD_UNIT
}

pub(crate) fn to_coefficient_array_post(
    value: &SIMDContent,
    out: &[i32],
    future_out: &[i32],
) -> bool {
    future_out == value
}

#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::fstar::after(r#"
    let bounded_add_pre (a b: t_Array i32 (sz 8)) (b1:nat) (b2:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\ b1 + b2 <= 4294967295))
                (ensures (Libcrux_ml_dsa.Simd.Traits.Specs.add_pre a b))
               [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.add_pre a b);
                SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
                SMTPat (Spec.Utils.is_i32b_array_opaque b2 b)] =
        reveal_opaque (`%$add_pre) ($add_pre)
    "#)]
pub(crate) fn add_pre(lhs: &SIMDContent, rhs: &SIMDContent) -> Prop {
    forall(|i: usize| {
        implies(
            i < COEFFICIENTS_IN_SIMD_UNIT,
            int_is_i32(lhs[i].to_int() + rhs[i].to_int()),
        )
    })
}

#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::fstar::after(r#"
    let bounded_add_post (a b a_future: t_Array i32 (sz 8)) (b1 b2 b3:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\
                    b1 + b2 <= b3 /\ Libcrux_ml_dsa.Simd.Traits.Specs.add_post a b a_future))
            (ensures (Spec.Utils.is_i32b_array_opaque b3 a_future))
            [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.add_post a b a_future);
            SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
            SMTPat (Spec.Utils.is_i32b_array_opaque b2 b);
            SMTPat (Spec.Utils.is_i32b_array_opaque b3 a_future)] =
        reveal_opaque (`%$add_post) ($add_post)
    "#)]
pub(crate) fn add_post(lhs: &SIMDContent, rhs: &SIMDContent, future_lhs: &SIMDContent) -> Prop {
    forall(|i: usize| {
        implies(
            i < COEFFICIENTS_IN_SIMD_UNIT,
            future_lhs[i].to_int() == (lhs[i].to_int() + rhs[i].to_int()),
        )
    })
}

#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::fstar::after(r#"
    let bounded_subtract_pre (a b: t_Array i32 (sz 8)) (b1:nat) (b2:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\ b1 + b2 <= 4294967295))
              (ensures (Libcrux_ml_dsa.Simd.Traits.Specs.subtract_pre a b))
              [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.subtract_pre a b);
               SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
               SMTPat (Spec.Utils.is_i32b_array_opaque b2 b)] =
        reveal_opaque (`%$subtract_pre) ($subtract_pre)
    "#)]
pub(crate) fn subtract_pre(lhs: &SIMDContent, rhs: &SIMDContent) -> Prop {
    forall(|i: usize| {
        implies(
            i < COEFFICIENTS_IN_SIMD_UNIT,
            int_is_i32(lhs[i].to_int() - rhs[i].to_int()),
        )
    })
}

#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::fstar::after(r#"
    let bounded_subtract_post (a b a_future: t_Array i32 (sz 8)) (b1 b2 b3:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\
                        b1 + b2 <= b3 /\ Libcrux_ml_dsa.Simd.Traits.Specs.subtract_post a b a_future))
                (ensures (Spec.Utils.is_i32b_array_opaque b3 a_future))
                [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.subtract_post a b a_future);
                SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
                SMTPat (Spec.Utils.is_i32b_array_opaque b2 b);
                SMTPat (Spec.Utils.is_i32b_array_opaque b3 a_future)] =
                reveal_opaque (`%$subtract_post) ($subtract_post)
    "#)]
pub(crate) fn subtract_post(
    lhs: &SIMDContent,
    rhs: &SIMDContent,
    future_lhs: &SIMDContent,
) -> Prop {
    forall(|i: usize| {
        implies(
            i < COEFFICIENTS_IN_SIMD_UNIT,
            future_lhs[i].to_int() == (lhs[i].to_int() - rhs[i].to_int()),
        )
    })
}

pub(crate) fn infinity_norm_exceeds_pre(simd_unit: &SIMDContent, bound: i32) -> Prop {
    hax_lib::fstar::prop!(
        r#"v $bound > 0 /\
        Spec.Utils.is_i32b_array_opaque (v ${FIELD_MAX}) (${simd_unit})"#
    )
}

pub(crate) fn infinity_norm_exceeds_post(
    simd_unit: &SIMDContent,
    bound: i32,
    result: bool,
) -> bool {
    true
}

pub(crate) fn decompose_pre(
    gamma2: Gamma2,
    simd_unit: &SIMDContent,
    low: &SIMDContent,
    high: &SIMDContent,
) -> Prop {
    hax_lib::fstar::prop!(
        r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${FIELD_MAX}) (${simd_unit})"#
    )
}
pub(crate) fn decompose_post(
    gamma2: Gamma2,
    simd_unit: &SIMDContent,
    low: &SIMDContent,
    high: &SIMDContent,
    future_low: &SIMDContent,
    future_high: &SIMDContent,
) -> bool {
    true
}

pub(crate) fn compute_hint_pre(
    low: &SIMDContent,
    high: &SIMDContent,
    gamma2: i32,
    hint: &SIMDContent,
) -> Prop {
    hax_lib::fstar::prop!(
        r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232})"#
    )
}

pub(crate) fn compute_hint_post(
    low: &SIMDContent,
    high: &SIMDContent,
    gamma2: i32,
    hint: &SIMDContent,
    future_hint: &SIMDContent,
    return_value: usize,
) -> bool {
    return_value <= 8
}

pub(crate) fn use_hint_pre(gamma2: Gamma2, simd_unit: &SIMDContent, hint: &SIMDContent) -> Prop {
    hax_lib::fstar::prop!(
        r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${FIELD_MAX}) ($simd_unit)"#
    )
}

pub(crate) fn use_hint_post(
    gamma2: Gamma2,
    simd_unit: &SIMDContent,
    hint: &SIMDContent,
    future_hint: &SIMDContent,
) -> bool {
    true
}

pub(crate) fn montgomery_multiply_pre(lhs: &SIMDContent, rhs: &SIMDContent) -> Prop {
    hax_lib::fstar::prop!(
        r#"
        Spec.Utils.is_i32b_array_opaque (v $FIELD_MAX) $rhs"#
    )
}

pub(crate) fn montgomery_multiply_post(
    lhs: &SIMDContent,
    rhs: &SIMDContent,
    future_lhs: &SIMDContent,
) -> Prop {
    hax_lib::fstar::prop!(
        r#"
        Spec.Utils.is_i32b_array_opaque (v $FIELD_MAX) $future_lhs /\
        Spec.MLDSA.Math.(forall i. i < 8 ==>
            mod_q (v (Seq.index ($future_lhs) i)) ==
            mod_q (v (Seq.index ($lhs) i) * v (Seq.index $rhs i) * 8265825))"#
    )
}

pub(crate) fn shift_left_then_reduce_pre<const SHIFT_BY: i32>(simd_unit: &SIMDContent) -> Prop {
    hax_lib::fstar::prop!(
        r#"v $SHIFT_BY == 13 /\
        (forall i. i < 8 ==> v (Seq.index (v $simd_unit) i) >= 0 /\
            v (Seq.index (v $simd_unit) i) <= 261631)"#
    )
}

pub(crate) fn shift_left_then_reduce_post<const SHIFT_BY: i32>(
    simd_unit: &SIMDContent,
    future_simd_unit: &SIMDContent,
) -> bool {
    true
}

pub(crate) fn power2round_pre(t0: &SIMDContent, t1: &SIMDContent) -> Prop {
    hax_lib::fstar::prop!(
        r#"
        Spec.Utils.is_i32b_array_opaque (v ${FIELD_MAX}) (v $t0)"#
    )
}

pub(crate) fn power2round_post(
    t0: &SIMDContent,
    t1: &SIMDContent,
    future_t0: &SIMDContent,
    future_t1: &SIMDContent,
) -> bool {
    true
}
