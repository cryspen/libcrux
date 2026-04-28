use crate::{
    constants::{Eta, Gamma2},
    simd::traits::*,
};

mod arithmetic;
mod vector_type;
// Some of the portable implementations are used in lieu of vectorized ones in
// the AVX2 module.
pub(crate) mod encoding;
mod invntt;
mod ntt;
mod sample;

use arithmetic::shift_left_then_reduce;
/// Portable SIMD coefficients
pub(crate) use vector_type::Coefficients as PortableSIMDUnit;
use vector_type::Coefficients;

#[cfg(hax)]
use crate::simd::traits::specs;

#[cfg(hax)]
impl Repr for Coefficients {
    fn repr(&self) -> [i32; COEFFICIENTS_IN_SIMD_UNIT] {
        self.values
    }
}

#[cfg(not(hax))]
impl Repr for Coefficients {}

#[hax_lib::attributes]
impl Operations for Coefficients {
    #[ensures(|result| result.repr() == [0i32; COEFFICIENTS_IN_SIMD_UNIT])]
    fn zero() -> Coefficients {
        vector_type::zero()
    }

    #[requires(array.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[ensures(|_| future(out).repr() == array)]
    fn from_coefficient_array(array: &[i32], out: &mut Coefficients) {
        vector_type::from_coefficient_array(array, out)
    }

    #[requires(out.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[ensures(|_| future(out) == value.repr())]
    fn to_coefficient_array(value: &Coefficients, out: &mut [i32]) {
        vector_type::to_coefficient_array(value, out)
    }

    #[requires(specs::add_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|_| specs::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn add(lhs: &mut Coefficients, rhs: &Coefficients) {
        arithmetic::add(lhs, rhs)
    }

    #[requires(specs::sub_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|_| specs::sub_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn subtract(lhs: &mut Coefficients, rhs: &Coefficients) {
        arithmetic::subtract(lhs, rhs)
    }

    #[requires(fstar!(r#"v $bound > 0 /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|result| fstar!(r#"
        Libcrux_ml_dsa.Simd.Traits.Specs.infinity_norm_exceeds_post
            (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) $bound $result"#))]
    fn infinity_norm_exceeds(simd_unit: &Coefficients, bound: i32) -> bool {
        hax_lib::fstar!("admit ()");
        arithmetic::infinity_norm_exceeds(simd_unit, bound)
    }

    #[requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.decompose_lane_post
            $gamma2
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${low}_future) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${high}_future) i))"#))]
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self) {
        hax_lib::fstar!("admit ()");
        arithmetic::decompose(gamma2, simd_unit, low, high)
    }

    #[requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232})"#))]
    #[ensures(|result| fstar!(r#"v $result <= 8 /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.compute_hint_lane_post
            $gamma2
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${low}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${high}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint}_future) i))"#))]
    fn compute_hint(
        low: &Coefficients,
        high: &Coefficients,
        gamma2: i32,
        hint: &mut Coefficients,
    ) -> usize {
        hax_lib::fstar!("admit ()");
        arithmetic::compute_hint(low, high, gamma2, hint)
    }

    #[requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) /\
        Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint})"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.use_hint_lane_post
            $gamma2
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint}_future) i))"#))]
    fn use_hint(gamma2: Gamma2, simd_unit: &Coefficients, hint: &mut Coefficients) {
        hax_lib::fstar!("admit ()");
        arithmetic::use_hint(gamma2, simd_unit, hint)
    }

    #[requires(fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (${rhs.repr()})"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}_future) /\
        Spec.MLDSA.Math.(forall i. i < 8 ==>
            mod_q (v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}_future) i)) ==
            mod_q (v (Seq.index (${lhs.repr()}) i) * v (Seq.index (${rhs.repr()}) i) * 8265825)) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.montgomery_multiply_lane_post
            (Seq.index (${lhs.repr()}) i)
            (Seq.index (${rhs.repr()}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}_future) i))"#))]
    fn montgomery_multiply(lhs: &mut Coefficients, rhs: &Coefficients) {
        hax_lib::fstar!("admit ()");
        arithmetic::montgomery_multiply(lhs, rhs);
    }

    #[requires(fstar!(r#"v $SHIFT_BY == 13 /\
        (forall i. i < 8 ==> v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i) >= 0 /\
            v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i) <= 261631)"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.shift_left_then_reduce_lane_post
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}_future) i))"#))]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Coefficients) {
        hax_lib::fstar!("admit ()");
        shift_left_then_reduce::<SHIFT_BY>(simd_unit);
    }

    #[requires(fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0})"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.power2round_lane_post
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}_future) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}_future) i))"#))]
    fn power2round(t0: &mut Coefficients, t1: &mut Coefficients) {
        hax_lib::fstar!("admit ()");
        arithmetic::power2round(t0, t1)
    }

    #[requires(fstar!(r#"
        Seq.length $randomness / 3 <= 4294967295 /\
        Seq.length $randomness / 3 <= Seq.length $out"#))]
    #[ensures(|result| fstar!(r#"v $result <= 8 /\
        (forall (i:nat{i < Seq.length ${out}_future}). i < v $result ==>
          v (Seq.index ${out}_future i) >= 0 /\
          v (Seq.index ${out}_future i) < 8380417)"#))]
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
        hax_lib::fstar!("admit ()");
        sample::rejection_sample_less_than_field_modulus(randomness, out)
    }

    #[requires(fstar!(r#"
        Seq.length $randomness * 2 <= 4294967295 /\
        Seq.length $randomness * 2 <= Seq.length $out"#))]
    #[ensures(|result| fstar!(r#"v $result <= 8 /\
        (forall (i:nat{i < Seq.length ${out}_future}). i < v $result ==>
          v (Seq.index ${out}_future i) >= -2 /\ v (Seq.index ${out}_future i) <= 2)"#))]
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
        hax_lib::fstar!("admit ()");
        sample::rejection_sample_less_than_eta_equals_2(randomness, out)
    }

    #[requires(fstar!(r#"
        Seq.length $randomness * 2 <= 4294967295 /\
        Seq.length $randomness * 2 <= Seq.length $out"#))]
    #[ensures(|result| fstar!(r#"v $result <= 8 /\
        (forall (i:nat{i < Seq.length ${out}_future}). i < v $result ==>
          v (Seq.index ${out}_future i) >= -4 /\ v (Seq.index ${out}_future i) <= 4)"#))]
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
        hax_lib::fstar!("admit ()");
        sample::rejection_sample_less_than_eta_equals_4(randomness, out)
    }

    #[requires(fstar!(r#"
        (v $gamma1_exponent == 17 \/ v $gamma1_exponent == 19) /\
        Seq.length $serialized == 1 + v $gamma1_exponent /\
        Spec.Utils.is_i32b_array_opaque (pow2 (v $gamma1_exponent)) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|_| fstar!(r#"
        Seq.length ${serialized}_future == Seq.length ${serialized}"#))]
    fn gamma1_serialize(simd_unit: &Coefficients, serialized: &mut [u8], gamma1_exponent: usize) {
        hax_lib::fstar!("admit ()");
        encoding::gamma1::serialize(simd_unit, serialized, gamma1_exponent)
    }

    #[requires(fstar!(r#"
        (v $gamma1_exponent == 17 \/ v $gamma1_exponent == 19) /\
        Seq.length $serialized == 1 + v $gamma1_exponent"#))]
    fn gamma1_deserialize(serialized: &[u8], out: &mut Coefficients, gamma1_exponent: usize) {
        hax_lib::fstar!("admit ()");
        encoding::gamma1::deserialize(serialized, out, gamma1_exponent)
    }

    #[requires(fstar!(r#"
        (Seq.length $serialized == 4 \/ Seq.length $serialized == 6) /\
        Spec.Utils.is_i32b_array_opaque (pow2 (Seq.length $serialized)) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|_| fstar!(r#"
        Seq.length ${serialized}_future == Seq.length ${serialized}"#))]
    fn commitment_serialize(simd_unit: &Coefficients, serialized: &mut [u8]) {
        hax_lib::fstar!("admit ()");
        encoding::commitment::serialize(simd_unit, serialized)
    }

    #[requires(fstar!(r#"
        Seq.length $serialized == (match $eta with
                                   | Libcrux_ml_dsa.Constants.Eta_Two -> 3
                                   | Libcrux_ml_dsa.Constants.Eta_Four -> 4) /\
        Spec.Utils.is_i32b_array_opaque (match $eta with
                                         | Libcrux_ml_dsa.Constants.Eta_Two -> 2
                                         | Libcrux_ml_dsa.Constants.Eta_Four -> 4)
                                        (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|_| fstar!(r#"
        Seq.length ${serialized}_future == Seq.length ${serialized}"#))]
    fn error_serialize(eta: Eta, simd_unit: &Coefficients, serialized: &mut [u8]) {
        hax_lib::fstar!("admit ()");
        encoding::error::serialize(eta, simd_unit, serialized)
    }

    #[requires(fstar!(r#"
        Seq.length $serialized == (match $eta with
                                   | Libcrux_ml_dsa.Constants.Eta_Two -> 3
                                   | Libcrux_ml_dsa.Constants.Eta_Four -> 4)"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          ($eta == Libcrux_ml_dsa.Constants.Eta_Two ==>
              v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) >= -2 /\
              v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) <= 2) /\
          ($eta == Libcrux_ml_dsa.Constants.Eta_Four ==>
              v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) >= -4 /\
              v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) <= 4))"#))]
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Coefficients) {
        hax_lib::fstar!("admit ()");
        encoding::error::deserialize(eta, serialized, out);
    }

    #[requires(fstar!(r#"
        Seq.length $out == 13 /\
        Spec.Utils.is_i32b_array_opaque (pow2 13) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|_| fstar!(r#"
        Seq.length ${out}_future == Seq.length ${out}"#))]
    fn t0_serialize(simd_unit: &Coefficients, out: &mut [u8]) {
        hax_lib::fstar!("admit ()");
        encoding::t0::serialize(simd_unit, out)
    }

    #[requires(serialized.len() == 13)]
    fn t0_deserialize(serialized: &[u8], out: &mut Coefficients) {
        hax_lib::fstar!("admit ()");
        encoding::t0::deserialize(serialized, out)
    }

    #[requires(out.len() == 10)]
    #[ensures(|_| fstar!(r#"
        Seq.length ${out}_future == Seq.length ${out}"#))]
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]) {
        hax_lib::fstar!("admit ()");
        encoding::t1::serialize(simd_unit, out);
    }

    #[requires(serialized.len() == 10)]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) >= 0 /\
          v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) < pow2 10)"#))]
    fn t1_deserialize(serialized: &[u8], out: &mut Self) {
        hax_lib::fstar!("admit ()");
        encoding::t1::deserialize(serialized, out);
    }

    #[requires(fstar!(r#"
        (forall (i:nat). i < 32 ==>
            Spec.Utils.is_i32b_array_opaque
            (v ${specs::NTT_BASE_BOUND})
            (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} i)))
    "#))]
    #[ensures(|_| fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units}_future i)))
    "#))]
    fn ntt(simd_units: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
        hax_lib::fstar!("admit ()");
        ntt::ntt(simd_units)
    }

    #[requires(fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} i)))
    "#))]
    #[ensures(|_| fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units}_future i)))
    "#))]
    fn invert_ntt_montgomery(simd_units: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
        hax_lib::fstar!("admit ()");
        invntt::invert_ntt_montgomery(simd_units)
    }

    #[ensures(|_| fstar!(r#"
        (forall (j:nat). j < 32 ==>
          Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
            Libcrux_ml_dsa.Simd.Traits.Specs.reduce_lane_post
              (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} j)) i)
              (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units}_future j)) i)))"#))]
    fn reduce(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]) {
        hax_lib::fstar!("admit ()");
        for i in 0..simd_units.len() {
            shift_left_then_reduce::<0>(&mut simd_units[i]);
        }
    }
}
