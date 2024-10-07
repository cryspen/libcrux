use crate::simd::traits::{Operations, SIMD_UNITS_IN_RING_ELEMENT};
use libcrux_intrinsics;

mod arithmetic;
mod encoding;
mod ntt;
mod rejection_sample;

#[derive(Clone, Copy)]
pub struct AVX2SIMDUnit {
    pub(crate) coefficients: libcrux_intrinsics::avx2::Vec256,
}

impl From<libcrux_intrinsics::avx2::Vec256> for AVX2SIMDUnit {
    fn from(coefficients: libcrux_intrinsics::avx2::Vec256) -> Self {
        Self { coefficients }
    }
}

impl Operations for AVX2SIMDUnit {
    fn ZERO() -> Self {
        libcrux_intrinsics::avx2::mm256_setzero_si256().into()
    }

    fn from_coefficient_array(coefficient_array: &[i32]) -> Self {
        libcrux_intrinsics::avx2::mm256_loadu_si256_i32(coefficient_array).into()
    }

    fn to_coefficient_array(&self) -> [i32; 8] {
        let mut coefficient_array = [0i32; 8];
        libcrux_intrinsics::avx2::mm256_storeu_si256_i32(&mut coefficient_array, self.coefficients);

        coefficient_array
    }

    fn add(lhs: &Self, rhs: &Self) -> Self {
        arithmetic::add(lhs.coefficients, rhs.coefficients).into()
    }

    fn subtract(lhs: &Self, rhs: &Self) -> Self {
        arithmetic::subtract(lhs.coefficients, rhs.coefficients).into()
    }

    fn montgomery_multiply_by_constant(simd_unit: Self, constant: i32) -> Self {
        arithmetic::montgomery_multiply_by_constant(simd_unit.coefficients, constant).into()
    }
    fn montgomery_multiply(lhs: Self, rhs: Self) -> Self {
        arithmetic::montgomery_multiply(lhs.coefficients, rhs.coefficients).into()
    }
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: Self) -> Self {
        arithmetic::shift_left_then_reduce::<SHIFT_BY>(simd_unit.coefficients).into()
    }

    fn power2round(simd_unit: Self) -> (Self, Self) {
        let (lower, upper) = arithmetic::power2round(simd_unit.coefficients);

        (lower.into(), upper.into())
    }

    fn infinity_norm_exceeds(simd_unit: Self, bound: i32) -> bool {
        arithmetic::infinity_norm_exceeds(simd_unit.coefficients, bound)
    }

    fn decompose<const GAMMA2: i32>(simd_unit: Self) -> (Self, Self) {
        let (lower, upper) = arithmetic::decompose::<GAMMA2>(simd_unit.coefficients);

        (lower.into(), upper.into())
    }

    fn compute_hint<const GAMMA2: i32>(low: Self, high: Self) -> (usize, Self) {
        let (count, hint) = arithmetic::compute_hint::<GAMMA2>(low.coefficients, high.coefficients);

        (count, hint.into())
    }
    fn use_hint<const GAMMA2: i32>(simd_unit: Self, hint: Self) -> Self {
        arithmetic::use_hint::<GAMMA2>(simd_unit.coefficients, hint.coefficients).into()
    }

    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
        rejection_sample::less_than_field_modulus::sample(randomness, out)
    }
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
        rejection_sample::less_than_eta::sample::<2>(randomness, out)
    }
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
        rejection_sample::less_than_eta::sample::<4>(randomness, out)
    }

    fn gamma1_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::gamma1::serialize::<OUTPUT_SIZE>(simd_unit.coefficients)
    }
    fn gamma1_deserialize<const GAMMA1_EXPONENT: usize>(serialized: &[u8]) -> Self {
        encoding::gamma1::deserialize::<GAMMA1_EXPONENT>(serialized).into()
    }

    fn commitment_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::commitment::serialize::<OUTPUT_SIZE>(simd_unit.coefficients)
    }

    fn error_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::error::serialize::<OUTPUT_SIZE>(simd_unit.coefficients)
    }
    fn error_deserialize<const ETA: usize>(serialized: &[u8]) -> Self {
        encoding::error::deserialize::<ETA>(serialized).into()
    }

    fn t0_serialize(simd_unit: Self) -> [u8; 13] {
        encoding::t0::serialize(simd_unit.coefficients)
    }
    fn t0_deserialize(serialized: &[u8]) -> Self {
        encoding::t0::deserialize(serialized).into()
    }

    fn t1_serialize(simd_unit: Self) -> [u8; 10] {
        encoding::t1::serialize(simd_unit.coefficients)
    }
    fn t1_deserialize(serialized: &[u8]) -> Self {
        encoding::t1::deserialize(serialized).into()
    }

    fn ntt(simd_units: [Self; SIMD_UNITS_IN_RING_ELEMENT]) -> [Self; SIMD_UNITS_IN_RING_ELEMENT] {
        let result = ntt::ntt(simd_units.map(|x| x.coefficients));

        result.map(|x| x.into())
    }

    fn invert_ntt_at_layer_0(
        simd_unit: Self,
        zeta0: i32,
        zeta1: i32,
        zeta2: i32,
        zeta3: i32,
    ) -> Self {
        ntt::invert_ntt_at_layer_0(simd_unit.coefficients, zeta0, zeta1, zeta2, zeta3).into()
    }
    fn invert_ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self {
        ntt::invert_ntt_at_layer_1(simd_unit.coefficients, zeta0, zeta1).into()
    }
    fn invert_ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self {
        ntt::invert_ntt_at_layer_2(simd_unit.coefficients, zeta).into()
    }
}
