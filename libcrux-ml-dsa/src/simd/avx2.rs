use crate::{
    constants::{Eta, Gamma2},
    simd::traits::*,
};

mod arithmetic;
mod encoding;
mod invntt;
mod ntt;
mod rejection_sample;
mod vector_type;

use arithmetic::shift_left_then_reduce;
pub(crate) use vector_type::{AVX2RingElement, Vec256 as AVX2SIMDUnit};

#[cfg(hax)]
#[hax_lib::attributes]
impl Repr for AVX2SIMDUnit {
    #[hax_lib::requires(true)]
    fn repr(&self) -> [i32; COEFFICIENTS_IN_SIMD_UNIT] {
        let mut result = [0i32; COEFFICIENTS_IN_SIMD_UNIT];
        vector_type::to_coefficient_array(self, &mut result);
        result
    }
}

#[cfg(not(hax))]
impl Repr for AVX2SIMDUnit {}

/// Implementing the [`Operations`] for AVX2.
#[hax_lib::attributes]
impl Operations for AVX2SIMDUnit {
    #[inline(always)]
    #[hax_lib::ensures(|result| specs::zero_post(&result.repr()))]
    fn zero() -> Self {
        let zero = vector_type::zero();
        hax_lib::fstar!(r#"Seq.lemma_eq_intro (${zero.repr()}) (${[0i32; 8]})"#);
        zero
    }

    #[inline(always)]
    #[hax_lib::requires(specs::from_coefficient_array_pre(array, &out.repr()))]
    #[hax_lib::ensures(|_| specs::from_coefficient_array_post(array, &out.repr(), &future(out).repr()))]
    fn from_coefficient_array(array: &[i32], out: &mut Self) {
        vector_type::from_coefficient_array(array, out);
        hax_lib::fstar!("Seq.lemma_eq_intro (${out.repr()}) array");
    }

    #[inline(always)]
    #[hax_lib::requires(specs::to_coefficient_array_pre(&value.repr(), out))]
    #[hax_lib::ensures(|_| specs::to_coefficient_array_post(&value.repr(), out, &future(out)))]
    fn to_coefficient_array(value: &Self, out: &mut [i32]) {
        vector_type::to_coefficient_array(value, out);
        hax_lib::fstar!("Seq.lemma_eq_intro (${value.repr()}) $out");
    }

    #[inline(always)]
    #[hax_lib::requires(specs::add_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn add(lhs: &mut Self, rhs: &Self) {
        hax_lib::fstar!("Spec.Intrinsics.reveal_opaque_arithmetic_ops #I32");
        hax_lib::fstar!("reveal_opaque (`%${specs::add_pre}) ${specs::add_pre}");
        hax_lib::fstar!("reveal_opaque (`%${specs::add_post}) ${specs::add_post}");
        arithmetic::add(&mut lhs.value, &rhs.value)
    }

    #[inline(always)]
    #[hax_lib::requires(specs::subtract_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::subtract_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn subtract(lhs: &mut Self, rhs: &Self) {
        hax_lib::fstar!("Spec.Intrinsics.reveal_opaque_arithmetic_ops #I32");
        hax_lib::fstar!("reveal_opaque (`%${specs::subtract_pre}) ${specs::subtract_pre}");
        hax_lib::fstar!("reveal_opaque (`%${specs::subtract_post}) ${specs::subtract_post}");
        arithmetic::subtract(&mut lhs.value, &rhs.value)
    }

    #[inline(always)]
    #[hax_lib::requires(specs::infinity_norm_exceeds_pre(&simd_unit.repr(), bound))]
    #[hax_lib::ensures(|result| specs::infinity_norm_exceeds_post(&simd_unit.repr(), bound, result))]
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool {
        hax_lib::fstar!(
            "reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) Spec.Utils.is_i32b_array_opaque"
        );
        arithmetic::infinity_norm_exceeds(&simd_unit.value, bound)
    }

    #[inline(always)]
    #[hax_lib::requires(specs::decompose_pre(gamma2, &simd_unit.repr(), &low.repr(), &high.repr()))]
    #[hax_lib::ensures(|_| specs::decompose_post(gamma2, &simd_unit.repr(), &low.repr(), &high.repr(), &future(low).repr(), &future(high).repr()))]
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self) {
        hax_lib::fstar!(
            "reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) Spec.Utils.is_i32b_array_opaque"
        );
        arithmetic::decompose(gamma2, &simd_unit.value, &mut low.value, &mut high.value);
    }

    #[inline(always)]
    #[hax_lib::requires(specs::compute_hint_pre(&low.repr(), &high.repr(), gamma2, &hint.repr()))]
    #[hax_lib::ensures(|result| specs::compute_hint_post(&low.repr(), &high.repr(), gamma2, &hint.repr(), &future(hint).repr(), result))]
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize {
        arithmetic::compute_hint(&low.value, &high.value, gamma2, &mut hint.value)
    }

    #[inline(always)]
    #[hax_lib::requires(specs::use_hint_pre(gamma2, &simd_unit.repr(), &hint.repr()))]
    #[hax_lib::ensures(|_| specs::use_hint_post(gamma2, &simd_unit.repr(), &hint.repr(), &future(hint).repr()))]
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self) {
        arithmetic::use_hint(gamma2, &simd_unit.value, &mut hint.value);
    }

    #[inline(always)]
    #[hax_lib::requires(specs::montgomery_multiply_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::montgomery_multiply_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self) {
        arithmetic::montgomery_multiply(&mut lhs.value, &rhs.value);
    }

    #[inline(always)]
    #[hax_lib::requires(specs::shift_left_then_reduce_pre::<SHIFT_BY>(&simd_unit.repr()))]
    #[hax_lib::ensures(|_| specs::shift_left_then_reduce_post::<SHIFT_BY>(&simd_unit.repr(), &future(simd_unit).repr()))]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self) {
        shift_left_then_reduce::<SHIFT_BY>(&mut simd_unit.value)
    }

    #[inline(always)]
    #[hax_lib::requires(specs::power2round_pre(&t0.repr(), &t1.repr()))]
    #[hax_lib::ensures(|_| specs::power2round_post(&t0.repr(), &t1.repr(), &future(t0).repr(), &future(t1).repr()))]
    fn power2round(t0: &mut Self, t1: &mut Self) {
        arithmetic::power2round(&mut t0.value, &mut t1.value);
    }

    #[inline(always)]
    #[hax_lib::requires(specs::rejection_sample_less_than_field_modulus_pre(randomness, out))]
    #[hax_lib::ensures(|result| specs::rejection_sample_less_than_field_modulus_post(randomness, out, future(out), result))]
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
        rejection_sample::less_than_field_modulus::sample(randomness, out)
    }

    #[inline(always)]
    #[hax_lib::requires(specs::rejection_sample_less_than_eta_equals_2_pre(randomness, out))]
    #[hax_lib::ensures(|result| specs::rejection_sample_less_than_eta_equals_2_post(randomness, out, future(out), result))]
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
        rejection_sample::less_than_eta::sample::<2>(randomness, out)
    }

    #[inline(always)]
    #[hax_lib::requires(specs::rejection_sample_less_than_eta_equals_4_pre(randomness, out))]
    #[hax_lib::ensures(|result| specs::rejection_sample_less_than_eta_equals_4_post(randomness, out, future(out), result))]
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
        rejection_sample::less_than_eta::sample::<4>(randomness, out)
    }

    #[inline(always)]
    #[hax_lib::requires(specs::gamma1_serialize_pre(&simd_unit.repr(), serialized, gamma1_exponent))]
    #[hax_lib::ensures(|_| specs::gamma1_serialize_post(&simd_unit.repr(), serialized, gamma1_exponent, future(serialized)))]
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize) {
        encoding::gamma1::serialize(&simd_unit.value, serialized, gamma1_exponent)
    }
    #[inline(always)]
    #[hax_lib::requires(specs::gamma1_deserialize_pre(serialized, &out.repr(), gamma1_exponent))]
    #[hax_lib::ensures(|_| specs::gamma1_deserialize_post(serialized, &out.repr(), gamma1_exponent, &future(out).repr()))]
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self, gamma1_exponent: usize) {
        encoding::gamma1::deserialize(serialized, &mut out.value, gamma1_exponent);
    }

    #[inline(always)]
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [u8]) {
        hax_lib::assume!(false);
        encoding::commitment::serialize(&simd_unit.value, serialized)
    }

    #[inline(always)]
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [u8]) {
        hax_lib::assume!(false);
        encoding::error::serialize(eta, &simd_unit.value, serialized)
    }

    #[inline(always)]
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self) {
        hax_lib::assume!(false);
        encoding::error::deserialize(eta, serialized, &mut out.value);
    }

    #[inline(always)]
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn t0_serialize(simd_unit: &Self, out: &mut [u8]) {
        hax_lib::assume!(false);
        // out len 13
        encoding::t0::serialize(&simd_unit.value, out);
    }
    #[inline(always)]
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn t0_deserialize(serialized: &[u8], out: &mut Self) {
        hax_lib::assume!(false);
        encoding::t0::deserialize(serialized, &mut out.value);
    }

    #[inline(always)]
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]) {
        hax_lib::assume!(false);
        encoding::t1::serialize(&simd_unit.value, out);
    }

    #[inline(always)]
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn t1_deserialize(serialized: &[u8], out: &mut Self) {
        hax_lib::assume!(false);
        encoding::t1::deserialize(serialized, &mut out.value);
    }

    #[inline(always)]
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn ntt(simd_units: &mut AVX2RingElement) {
        hax_lib::assume!(false);
        ntt::ntt(simd_units);
    }

    #[inline(always)]
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn invert_ntt_montgomery(simd_units: &mut AVX2RingElement) {
        hax_lib::assume!(false);
        invntt::invert_ntt_montgomery(simd_units);
    }

    #[inline(always)]
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn reduce(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]) {
        hax_lib::assume!(false);
        shift_left_then_reduce::<0>(&mut simd_units[0].value);
        shift_left_then_reduce::<0>(&mut simd_units[8].value);
        shift_left_then_reduce::<0>(&mut simd_units[16].value);
        shift_left_then_reduce::<0>(&mut simd_units[24].value);
    }
}
