use crate::simd::traits::{Operations, SIMD_UNITS_IN_RING_ELEMENT};

mod arithmetic;
mod vector_type;
// Some of the portable implementations are used in lieu of vectorized ones in
// the AVX2 module.
pub(crate) mod encoding;
mod invntt;
mod ntt;
mod sample;

use vector_type::Coefficients;
pub(crate) use vector_type::PortableSIMDUnit;

use super::traits::Eta;

impl Operations for PortableSIMDUnit {
    type Coefficient = Coefficients;

    fn zero() -> Coefficients {
        vector_type::zero()
    }

    fn from_coefficient_array(array: &[i32], out: &mut Coefficients) {
        vector_type::from_coefficient_array(array, out)
    }

    fn to_coefficient_array(value: &Coefficients, out: &mut [i32]) {
        vector_type::to_coefficient_array(value, out)
    }

    fn add(lhs: &mut Coefficients, rhs: &Coefficients) {
        arithmetic::add(lhs, rhs)
    }

    fn subtract(lhs: &mut Coefficients, rhs: &Coefficients) {
        arithmetic::subtract(lhs, rhs)
    }

    fn montgomery_multiply(lhs: &mut Coefficients, rhs: &Coefficients) {
        arithmetic::montgomery_multiply(lhs, rhs);
    }

    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Coefficients) {
        arithmetic::shift_left_then_reduce::<SHIFT_BY>(simd_unit);
    }

    fn power2round(t0: &mut Coefficients, t1: &mut Coefficients) {
        arithmetic::power2round(t0, t1)
    }

    fn infinity_norm_exceeds(simd_unit: &Coefficients, bound: i32) -> bool {
        arithmetic::infinity_norm_exceeds(simd_unit, bound)
    }

    fn decompose<const GAMMA2: i32>(
        simd_unit: &Self::Coefficient,
        low: &mut Self::Coefficient,
        high: &mut Self::Coefficient,
    ) {
        arithmetic::decompose::<GAMMA2>(simd_unit, low, high)
    }

    fn compute_hint<const GAMMA2: i32>(
        low: &Coefficients,
        high: &Coefficients,
        hint: &mut Self::Coefficient,
    ) -> usize {
        arithmetic::compute_hint::<GAMMA2>(low, high, hint)
    }

    fn use_hint<const GAMMA2: i32>(simd_unit: &Coefficients, hint: &mut Coefficients) {
        arithmetic::use_hint::<GAMMA2>(simd_unit, hint)
    }

    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
        sample::rejection_sample_less_than_field_modulus(randomness, out)
    }

    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
        sample::rejection_sample_less_than_eta_equals_2(randomness, out)
    }

    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
        sample::rejection_sample_less_than_eta_equals_4(randomness, out)
    }

    fn gamma1_serialize<const GAMMA1_EXPONENT: usize>(
        simd_unit: &Coefficients,
        serialized: &mut [u8],
    ) {
        encoding::gamma1::serialize::<GAMMA1_EXPONENT>(simd_unit, serialized)
    }

    fn gamma1_deserialize<const GAMMA1_EXPONENT: usize>(serialized: &[u8], out: &mut Coefficients) {
        encoding::gamma1::deserialize::<GAMMA1_EXPONENT>(serialized, out)
    }

    fn commitment_serialize(simd_unit: &Coefficients, serialized: &mut [u8]) {
        encoding::commitment::serialize(simd_unit, serialized)
    }

    fn error_serialize(eta: Eta, simd_unit: &Coefficients, serialized: &mut [u8]) {
        encoding::error::serialize(eta, simd_unit, serialized)
    }

    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Coefficients) {
        encoding::error::deserialize(eta, serialized, out);
    }

    fn t0_serialize(simd_unit: &Coefficients, out: &mut [u8]) {
        encoding::t0::serialize(simd_unit, out)
    }

    fn t0_deserialize(serialized: &[u8], out: &mut Coefficients) {
        encoding::t0::deserialize(serialized, out)
    }

    fn t1_serialize(simd_unit: &Self::Coefficient, out: &mut [u8]) {
        encoding::t1::serialize(simd_unit, out);
    }

    fn t1_deserialize(serialized: &[u8], out: &mut Self::Coefficient) {
        encoding::t1::deserialize(serialized, out);
    }

    fn ntt(simd_units: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
        ntt::ntt(simd_units)
    }

    fn invert_ntt_montgomery(simd_units: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
        invntt::invert_ntt_montgomery(simd_units)
    }
}
