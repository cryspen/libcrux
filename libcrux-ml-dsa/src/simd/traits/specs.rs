use crate::constants::{Eta, Gamma2, BITS_IN_LOWER_PART_OF_T, GAMMA2_V261_888, GAMMA2_V95_232};
use hax_lib::*;

pub(crate) const PRIME: u32 = 8380417;

pub(crate) const MONT_R: u32 = 8380417;

pub(crate) const FIELD_MODULUS: i32 = 8_380_417;

pub(crate) const FIELD_MAX: u32 = 8380416;

pub(crate) const FIELD_MID: u32 = 4190208;

pub(crate) const NTT_BASE_BOUND: u32 = FIELD_MID;

const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

const SIMD_UNITS_IN_RING_ELEMENT: usize = 32;

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
        Spec.Utils.is_i32b_array_opaque (v $FIELD_MAX) $simd_unit"#
    )
}

pub(crate) fn infinity_norm_exceeds_post(
    simd_unit: &SIMDContent,
    bound: i32,
    result: bool,
) -> Prop {
    hax_lib::fstar::prop!(
        r#" $result == false ==>
        Spec.Utils.is_i32b_array_opaque (v $bound - 1) $simd_unit "#
    )
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
        Spec.Utils.is_i32b_array_opaque (v $FIELD_MAX) $simd_unit"#
    )
}
pub(crate) fn decompose_post(
    gamma2: Gamma2,
    simd_unit: &SIMDContent,
    low: &SIMDContent,
    high: &SIMDContent,
    future_low: &SIMDContent,
    future_high: &SIMDContent,
) -> Prop {
    hax_lib::fstar::prop!(
        r#"forall i. i < 8 ==>
        (let r  = v (Seq.index $simd_unit i) in
         let r0 = v (Seq.index $future_low i) in
         let r1 = v (Seq.index $future_high i) in
         let (r0_s, r1_s, cond) = Spec.MLDSA.Math.decompose (v $gamma2) r in
         r0 = r0_s /\
         r1 = r1_s /\
         (if cond then
             (r0 >= -(v $gamma2) /\ r0 < 0)
          else
             (r0 > -(v $gamma2) /\ r0 <= v $gamma2)) /\
         (r1 >= 0 /\ r1 < (v $FIELD_MAX) / (v $gamma2 * 2)))"#
    )
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
    result: usize,
) -> Prop {
    hax_lib::fstar::prop!(
        r#"
    (forall i. i < 8 ==> (v (Seq.index future_hint i) =
        Spec.MLDSA.Math.compute_one_hint (v (Seq.index $low i))
            (v (Seq.index high i)) (v $gamma2)))
    /\ v $result == Spec.MLDSA.Math.compute_hint future_hint
    /\ v $result <= 8 "#
    )
}

pub(crate) fn use_hint_pre(gamma2: Gamma2, simd_unit: &SIMDContent, hint: &SIMDContent) -> Prop {
    hax_lib::fstar::prop!(
        r#"(v $gamma2 == v $GAMMA2_V261_888 \/ v $gamma2 == v $GAMMA2_V95_232) /\
    Spec.Utils.is_i32b_array_opaque (v $FIELD_MODULUS - 1) $simd_unit /\
    (forall i. i < 8 ==> v (Seq.index $hint i) == 0 \/ v (Seq.index $hint i) == 1)"#
    )
}

pub(crate) fn use_hint_post(
    gamma2: Gamma2,
    simd_unit: &SIMDContent,
    hint: &SIMDContent,
    future_hint: &SIMDContent,
) -> Prop {
    hax_lib::fstar::prop!(
        r#"forall i. i < 8 ==>
        (let h = Seq.index $hint i in
         let result = Seq.index $future_hint i in
         v result = Spec.MLDSA.Math.use_one_hint (v $gamma2) (v (Seq.index $simd_unit i)) (v h))"#
    )
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
        (forall i. i < 8 ==> v (Seq.index $simd_unit i) >= 0 /\
            v (Seq.index $simd_unit i) <= 261631)"#
    )
}

pub(crate) fn shift_left_then_reduce_post<const SHIFT_BY: i32>(
    simd_unit: &SIMDContent,
    future_simd_unit: &SIMDContent,
) -> Prop {
    hax_lib::fstar::prop!(
        r#"
    Spec.Utils.is_i32b_array_opaque 8380416 ($future_simd_unit) /\
    (forall i. i < 8 ==> Spec.MLDSA.Math.(
        mod_q (v (Seq.index $future_simd_unit i)) ==
        mod_q (v ((Seq.index $simd_unit i) <<! v_SHIFT_BY))))
    "#
    )
}

pub(crate) fn power2round_pre(t0: &SIMDContent, t1: &SIMDContent) -> Prop {
    hax_lib::fstar::prop!(r#" Spec.Utils.is_i32b_array_opaque (v $FIELD_MAX) $t0"#)
}

pub(crate) fn power2round_post(
    t0: &SIMDContent,
    t1: &SIMDContent,
    future_t0: &SIMDContent,
    future_t1: &SIMDContent,
) -> Prop {
    hax_lib::fstar::prop!(
        r#"
    forall i. i < 8 ==>
        (let t0_v         = v (Seq.index $future_t0 i) in
         let (t0_s, t1_s) = Spec.MLDSA.Math.power2round (v (Seq.index $t0 i)) in
         t0_v == t0_s
         /\ v (Seq.index $future_t1 i) == t1_s
         /\ Spec.Utils.is_intb_bt (pow2 (v $BITS_IN_LOWER_PART_OF_T - 1)) t0_v)"#
    )
}

pub(crate) fn rejection_sample_less_than_field_modulus_pre(randomness: &[u8], out: &[i32]) -> bool {
    true
}

pub(crate) fn rejection_sample_less_than_field_modulus_post(
    randomness: &[u8],
    out: &[i32],
    return_value: usize,
) -> bool {
    true
}

pub(crate) fn rejection_sample_less_than_eta_equals_2_pre(randomness: &[u8], out: &[i32]) -> bool {
    true
}

pub(crate) fn rejection_sample_less_than_eta_equals_2_post(
    randomness: &[u8],
    out: &[i32],
    return_value: usize,
) -> bool {
    true
}

pub(crate) fn rejection_sample_less_than_eta_equals_4_pre(randomness: &[u8], out: &[i32]) -> bool {
    true
}

pub(crate) fn rejection_sample_less_than_eta_equals_4_post(
    randomness: &[u8],
    out: &[i32],
    return_value: usize,
) -> bool {
    true
}

pub(crate) fn gamma1_serialize_pre(
    simd_unit: &SIMDContent,
    serialized: &[u8],
    gamma1_exponent: usize,
) -> bool {
    true
}

pub(crate) fn gamma1_serialize_post(
    simd_unit: &SIMDContent,
    serialized: &[u8],
    gamma1_exponent: usize,
) -> bool {
    true
}

pub(crate) fn gamma1_deserialize_pre(
    serialized: &[u8],
    out: &SIMDContent,
    gamma1_exponent: usize,
) -> bool {
    true
}

pub(crate) fn gamma1_deserialize_post(
    serialized: &[u8],
    out: &SIMDContent,
    gamma1_exponent: usize,
    future_out: &SIMDContent,
) -> bool {
    true
}

pub(crate) fn commitment_serialize_pre(simd_unit: &SIMDContent, serialized: &[u8]) -> bool {
    serialized.len() == 4 || serialized.len() == 6
}

pub(crate) fn commitment_serialize_post(
    simd_unit: &SIMDContent,
    serialized: &[u8],
    future_serialized: &[u8],
) -> bool {
    future_serialized.len() == serialized.len()
}

pub(crate) fn error_serialize_pre(eta: Eta, simd_unit: &SIMDContent, serialized: &[u8]) -> bool {
    true
}

pub(crate) fn error_serialize_post(
    eta: Eta,
    simd_unit: &SIMDContent,
    serialized: &[u8],
    future_serialized: &[u8],
) -> bool {
    true
}

pub(crate) fn error_deserialize_pre(eta: Eta, serialized: &[u8], out: &SIMDContent) -> bool {
    true
}

pub(crate) fn error_deserialize_post(
    eta: Eta,
    serialized: &[u8],
    out: &SIMDContent,
    future_out: &SIMDContent,
) -> bool {
    true
}

pub(crate) fn t0_serialize_pre(simd_unit: &SIMDContent, out: &[u8]) -> bool {
    true
}

pub(crate) fn t0_serialize_post(simd_unit: &SIMDContent, out: &[u8], future_out: &[u8]) -> bool {
    true
}

pub(crate) fn t0_deserialize_pre(serialized: &[u8], out: &SIMDContent) -> bool {
    true
}

pub(crate) fn t0_deserialize_post(
    serialized: &[u8],
    out: &SIMDContent,
    future_out: &SIMDContent,
) -> bool {
    true
}

pub(crate) fn t1_serialize_pre(simd_unit: &SIMDContent, out: &[u8]) -> bool {
    true
}

pub(crate) fn t1_serialize_post(simd_unit: &SIMDContent, out: &[u8], future_out: &[u8]) -> bool {
    true
}

pub(crate) fn t1_deserialize_pre(serialized: &[u8], out: &SIMDContent) -> bool {
    true
}

pub(crate) fn t1_deserialize_post(
    serialized: &[u8],
    out: &SIMDContent,
    future_out: &SIMDContent,
) -> bool {
    true
}

pub(crate) fn ntt_pre(simd_units: &[SIMDContent; SIMD_UNITS_IN_RING_ELEMENT]) -> Prop {
    hax_lib::fstar::prop!(
        r#"
        (forall (i:nat). i < 32 ==>
            Spec.Utils.is_i32b_array_opaque
            (v ${NTT_BASE_BOUND})
            (Seq.index ${simd_units} i))
    "#
    )
}

pub(crate) fn ntt_post(
    simd_units: &[SIMDContent; SIMD_UNITS_IN_RING_ELEMENT],
    future_simd_units: &[SIMDContent; SIMD_UNITS_IN_RING_ELEMENT],
) -> Prop {
    hax_lib::fstar::prop!(
        r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${FIELD_MAX})
            (Seq.index ${future_simd_units} i))
    "#
    )
}

pub(crate) fn invert_ntt_montgomery_pre(
    simd_units: &[SIMDContent; SIMD_UNITS_IN_RING_ELEMENT],
) -> Prop {
    hax_lib::fstar::prop!(
        r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${FIELD_MAX})
            (Seq.index ${simd_units} i))
    "#
    )
}

pub(crate) fn invert_ntt_montgomery_post(
    simd_units: &[SIMDContent; SIMD_UNITS_IN_RING_ELEMENT],
    future_simd_units: &[SIMDContent; SIMD_UNITS_IN_RING_ELEMENT],
) -> Prop {
    hax_lib::fstar::prop!(
        r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${FIELD_MAX})
            (Seq.index ${future_simd_units} i))
    "#
    )
}

pub(crate) fn reduce_pre(simd_units: &[SIMDContent; SIMD_UNITS_IN_RING_ELEMENT]) -> bool {
    true
}

pub(crate) fn reduce_post(
    simd_units: &[SIMDContent; SIMD_UNITS_IN_RING_ELEMENT],
    future_simd_units: &[SIMDContent; SIMD_UNITS_IN_RING_ELEMENT],
) -> bool {
    true
}
