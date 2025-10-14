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
impl Repr for Coefficients {
    fn repr(&self) -> [i32; COEFFICIENTS_IN_SIMD_UNIT] {
        self.values
    }
}

#[cfg(not(hax))]
impl Repr for Coefficients {}

#[hax_lib::attributes]
impl Operations for Coefficients {
    #[hax_lib::ensures(|result| specs::zero_post(&result.repr()))]
    fn zero() -> Coefficients {
        vector_type::zero()
    }

    #[hax_lib::requires(specs::from_coefficient_array_pre(array, &out.repr()))]
    #[hax_lib::ensures(|_| specs::from_coefficient_array_post(array, &out.repr(), &future(out).repr()))]
    fn from_coefficient_array(array: &[i32], out: &mut Coefficients) {
        vector_type::from_coefficient_array(array, out)
    }

    #[hax_lib::requires(specs::to_coefficient_array_pre(&value.repr(), out))]
    #[hax_lib::ensures(|_| specs::to_coefficient_array_post(&value.repr(), out, &future(out)))]
    fn to_coefficient_array(value: &Coefficients, out: &mut [i32]) {
        vector_type::to_coefficient_array(value, out)
    }

    #[hax_lib::requires(specs::add_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn add(lhs: &mut Coefficients, rhs: &Coefficients) {
        arithmetic::add(lhs, rhs)
    }

    #[hax_lib::requires(specs::subtract_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::subtract_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn subtract(lhs: &mut Coefficients, rhs: &Coefficients) {
        arithmetic::subtract(lhs, rhs)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn infinity_norm_exceeds(simd_unit: &Coefficients, bound: i32) -> bool {
        hax_lib::assume!(false);
        arithmetic::infinity_norm_exceeds(simd_unit, bound)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self) {
        hax_lib::assume!(false);
        arithmetic::decompose(gamma2, simd_unit, low, high)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn compute_hint(
        low: &Coefficients,
        high: &Coefficients,
        gamma2: i32,
        hint: &mut Coefficients,
    ) -> usize {
        hax_lib::assume!(false);
        arithmetic::compute_hint(low, high, gamma2, hint)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn use_hint(gamma2: Gamma2, simd_unit: &Coefficients, hint: &mut Coefficients) {
        hax_lib::assume!(false);
        arithmetic::use_hint(gamma2, simd_unit, hint)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn montgomery_multiply(lhs: &mut Coefficients, rhs: &Coefficients) {
        hax_lib::assume!(false);
        arithmetic::montgomery_multiply(lhs, rhs);
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Coefficients) {
        hax_lib::assume!(false);
        shift_left_then_reduce::<SHIFT_BY>(simd_unit);
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn power2round(t0: &mut Coefficients, t1: &mut Coefficients) {
        hax_lib::assume!(false);
        arithmetic::power2round(t0, t1)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
        hax_lib::assume!(false);
        sample::rejection_sample_less_than_field_modulus(randomness, out)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
        hax_lib::assume!(false);
        sample::rejection_sample_less_than_eta_equals_2(randomness, out)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
        hax_lib::assume!(false);
        sample::rejection_sample_less_than_eta_equals_4(randomness, out)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn gamma1_serialize(simd_unit: &Coefficients, serialized: &mut [u8], gamma1_exponent: usize) {
        hax_lib::assume!(false);
        encoding::gamma1::serialize(simd_unit, serialized, gamma1_exponent)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn gamma1_deserialize(serialized: &[u8], out: &mut Coefficients, gamma1_exponent: usize) {
        hax_lib::assume!(false);
        encoding::gamma1::deserialize(serialized, out, gamma1_exponent)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn commitment_serialize(simd_unit: &Coefficients, serialized: &mut [u8]) {
        hax_lib::assume!(false);
        encoding::commitment::serialize(simd_unit, serialized)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn error_serialize(eta: Eta, simd_unit: &Coefficients, serialized: &mut [u8]) {
        hax_lib::assume!(false);
        encoding::error::serialize(eta, simd_unit, serialized)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Coefficients) {
        hax_lib::assume!(false);
        encoding::error::deserialize(eta, serialized, out);
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn t0_serialize(simd_unit: &Coefficients, out: &mut [u8]) {
        hax_lib::assume!(false);
        encoding::t0::serialize(simd_unit, out)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn t0_deserialize(serialized: &[u8], out: &mut Coefficients) {
        hax_lib::assume!(false);
        encoding::t0::deserialize(serialized, out)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]) {
        hax_lib::assume!(false);
        encoding::t1::serialize(simd_unit, out);
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn t1_deserialize(serialized: &[u8], out: &mut Self) {
        hax_lib::assume!(false);
        encoding::t1::deserialize(serialized, out);
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn ntt(simd_units: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
        hax_lib::assume!(false);
        ntt::ntt(simd_units)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn invert_ntt_montgomery(simd_units: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
        hax_lib::assume!(false);
        invntt::invert_ntt_montgomery(simd_units)
    }

    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| false)]
    fn reduce(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]) {
        hax_lib::assume!(false);
        for i in 0..simd_units.len() {
            shift_left_then_reduce::<0>(&mut simd_units[i]);
        }
    }
}
