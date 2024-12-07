use crate::simd::traits::{Operations, SIMD_UNITS_IN_RING_ELEMENT};

mod arithmetic;
mod vector_type;
// Some of the portable implementations are used in lieu of vectorized ones in
// the AVX2 module.
pub(crate) mod encoding;
mod invntt;
mod ntt;
mod sample;

pub(crate) use vector_type::PortableSIMDUnit;

impl Operations for PortableSIMDUnit {
    fn ZERO() -> Self {
        vector_type::ZERO()
    }

    fn from_coefficient_array(array: &[i32]) -> Self {
        vector_type::from_coefficient_array(array)
    }

    fn to_coefficient_array(&self) -> [i32; 8] {
        vector_type::to_coefficient_array(&self)
    }

    fn add(lhs: &Self, rhs: &Self) -> Self {
        arithmetic::add(lhs, rhs)
    }

    fn subtract(lhs: &Self, rhs: &Self) -> Self {
        arithmetic::subtract(lhs, rhs)
    }

    fn montgomery_multiply(lhs: Self, rhs: Self) -> Self {
        arithmetic::montgomery_multiply(&lhs, &rhs)
    }

    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: Self) -> Self {
        arithmetic::shift_left_then_reduce::<SHIFT_BY>(simd_unit)
    }

    fn power2round(simd_unit: Self) -> (Self, Self) {
        arithmetic::power2round(simd_unit)
    }

    fn infinity_norm_exceeds(simd_unit: Self, bound: i32) -> bool {
        arithmetic::infinity_norm_exceeds(simd_unit, bound)
    }

    fn decompose<const GAMMA2: i32>(simd_unit: Self) -> (Self, Self) {
        arithmetic::decompose::<GAMMA2>(simd_unit)
    }

    fn compute_hint<const GAMMA2: i32>(low: Self, high: Self) -> (usize, Self) {
        arithmetic::compute_hint::<GAMMA2>(low, high)
    }
    fn use_hint<const GAMMA2: i32>(simd_unit: Self, hint: Self) -> Self {
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

    fn gamma1_serialize<const GAMMA1_EXPONENT: usize>(simd_unit: Self, serialized: &mut [u8]) {
        encoding::gamma1::serialize::<GAMMA1_EXPONENT>(simd_unit, serialized)
    }
    fn gamma1_deserialize<const GAMMA1_EXPONENT: usize>(serialized: &[u8]) -> Self {
        encoding::gamma1::deserialize::<GAMMA1_EXPONENT>(serialized)
    }

    fn commitment_serialize(simd_unit: Self, serialized: &mut [u8]) {
        encoding::commitment::serialize(simd_unit, serialized)
    }

    fn error_serialize<const ETA: usize>(simd_unit: Self, serialized: &mut [u8]) {
        encoding::error::serialize::<ETA>(simd_unit, serialized)
    }
    fn error_deserialize<const ETA: usize>(serialized: &[u8]) -> Self {
        encoding::error::deserialize::<ETA>(serialized)
    }

    fn t0_serialize(simd_unit: Self) -> [u8; 13] {
        encoding::t0::serialize(simd_unit)
    }
    fn t0_deserialize(serialized: &[u8]) -> Self {
        encoding::t0::deserialize(serialized)
    }

    fn t1_serialize(simd_unit: Self) -> [u8; 10] {
        encoding::t1::serialize(simd_unit)
    }
    fn t1_deserialize(serialized: &[u8]) -> Self {
        encoding::t1::deserialize(serialized)
    }

    fn ntt(simd_units: [Self; SIMD_UNITS_IN_RING_ELEMENT]) -> [Self; SIMD_UNITS_IN_RING_ELEMENT] {
        ntt::ntt(simd_units)
    }

    fn invert_ntt_montgomery(
        simd_units: [Self; SIMD_UNITS_IN_RING_ELEMENT],
    ) -> [Self; SIMD_UNITS_IN_RING_ELEMENT] {
        invntt::invert_ntt_montgomery(simd_units)
    }
}
