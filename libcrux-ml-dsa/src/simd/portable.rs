use crate::simd::traits::Operations;

mod arithmetic;
mod encoding;
mod ntt;
mod sample;
mod simd_unit_type;

pub(crate) use simd_unit_type::PortableSIMDUnit;

impl Operations for PortableSIMDUnit {
    fn ZERO() -> Self {
        simd_unit_type::ZERO()
    }

    fn from_i32_array(array: &[i32]) -> Self {
        simd_unit_type::from_i32_array(array)
    }

    fn to_i32_array(simd_unit: Self) -> [i32; 8] {
        simd_unit_type::to_i32_array(simd_unit)
    }

    fn add(lhs: &Self, rhs: &Self) -> Self {
        arithmetic::add(lhs, rhs)
    }

    fn subtract(lhs: &Self, rhs: &Self) -> Self {
        arithmetic::subtract(lhs, rhs)
    }

    fn montgomery_multiply_by_constant(simd_unit: Self, c: i32) -> Self {
        arithmetic::montgomery_multiply_by_constant(simd_unit, c)
    }
    fn montgomery_multiply(lhs: Self, rhs: Self) -> Self {
        arithmetic::montgomery_multiply(&lhs, &rhs)
    }
    fn shift_left_then_reduce(simd_unit: Self, shift_by: usize) -> Self {
        arithmetic::shift_left_then_reduce(simd_unit, shift_by)
    }

    fn power2round(simd_unit: Self) -> (Self, Self) {
        arithmetic::power2round(simd_unit)
    }

    fn infinity_norm_exceeds(simd_unit: Self, bound: i32) -> bool {
        arithmetic::infinity_norm_exceeds(simd_unit, bound)
    }

    fn compute_hint<const GAMMA2: i32>(low: Self, high: Self) -> (usize, Self) {
        arithmetic::compute_hint::<GAMMA2>(low, high)
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

    fn gamma1_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::gamma1::serialize(simd_unit)
    }
    fn gamma1_deserialize<const GAMMA1_EXPONENT: usize>(serialized: &[u8]) -> Self {
        encoding::gamma1::deserialize::<GAMMA1_EXPONENT>(serialized)
    }

    fn commitment_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::commitment::serialize(simd_unit)
    }

    fn error_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::error::serialize(simd_unit)
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

    fn ntt_at_layer_0(simd_unit: Self, zeta0: i32, zeta1: i32, zeta2: i32, zeta3: i32) -> Self {
        ntt::ntt_at_layer_0(simd_unit, zeta0, zeta1, zeta2, zeta3)
    }
    fn ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self {
        ntt::ntt_at_layer_1(simd_unit, zeta0, zeta1)
    }
    fn ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self {
        ntt::ntt_at_layer_2(simd_unit, zeta)
    }

    fn invert_ntt_at_layer_0(
        simd_unit: Self,
        zeta0: i32,
        zeta1: i32,
        zeta2: i32,
        zeta3: i32,
    ) -> Self {
        ntt::invert_ntt_at_layer_0(simd_unit, zeta0, zeta1, zeta2, zeta3)
    }
    fn invert_ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self {
        ntt::invert_ntt_at_layer_1(simd_unit, zeta0, zeta1)
    }
    fn invert_ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self {
        ntt::invert_ntt_at_layer_2(simd_unit, zeta)
    }
}
