use crate::simd::traits::{Operations, SIMD_UNITS_IN_RING_ELEMENT};

mod arithmetic;
mod encoding;
mod invntt;
mod ntt;
mod rejection_sample;
mod vector_type;

use vector_type::Vec256;
pub(crate) use vector_type::{AVX2RingElement, AVX2SIMDUnit};

impl Operations for AVX2SIMDUnit {
    type Coefficient = Vec256;

    #[inline(always)]
    fn ZERO() -> Vec256 {
        vector_type::zero()
    }

    #[inline(always)]
    fn from_coefficient_array(coefficient_array: &[i32]) -> Vec256 {
        vector_type::from_coefficient_array(coefficient_array)
    }

    #[inline(always)]
    fn to_coefficient_array(value: &Vec256, out: &mut [i32]) {
        vector_type::to_coefficient_array(value, out)
    }
    #[inline(always)]
    fn add(lhs: &Vec256, rhs: &Vec256) -> Vec256 {
        arithmetic::add(lhs, rhs)
    }
    #[inline(always)]
    fn subtract(lhs: &Vec256, rhs: &Vec256) -> Vec256 {
        arithmetic::subtract(lhs, rhs)
    }

    #[inline(always)]
    fn montgomery_multiply(lhs: &mut Vec256, rhs: &Vec256) {
        arithmetic::montgomery_multiply(lhs, rhs);
    }
    #[inline(always)]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Vec256) {
        arithmetic::shift_left_then_reduce::<SHIFT_BY>(simd_unit)
    }

    #[inline(always)]
    fn power2round(t0: &mut Vec256, t1: &mut Vec256) {
        arithmetic::power2round(t0, t1);
    }

    #[inline(always)]
    fn infinity_norm_exceeds(simd_unit: &Vec256, bound: i32) -> bool {
        arithmetic::infinity_norm_exceeds(simd_unit, bound)
    }

    #[inline(always)]
    fn decompose<const GAMMA2: i32>(simd_unit: &Vec256, low: &mut Vec256, high: &mut Vec256) {
        arithmetic::decompose::<GAMMA2>(simd_unit, low, high);
    }

    #[inline(always)]
    fn compute_hint<const GAMMA2: i32>(low: &Vec256, high: &Vec256) -> (usize, Vec256) {
        arithmetic::compute_hint::<GAMMA2>(low, high)
    }
    #[inline(always)]
    fn use_hint<const GAMMA2: i32>(simd_unit: &Vec256, hint: &mut Vec256) {
        arithmetic::use_hint::<GAMMA2>(simd_unit, hint);
    }

    #[inline(always)]
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
        rejection_sample::less_than_field_modulus::sample(randomness, out)
    }
    #[inline(always)]
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
        rejection_sample::less_than_eta::sample::<2>(randomness, out)
    }
    #[inline(always)]
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
        rejection_sample::less_than_eta::sample::<4>(randomness, out)
    }

    #[inline(always)]
    fn gamma1_serialize<const GAMMA1_EXPONENT: usize>(simd_unit: &Vec256, serialized: &mut [u8]) {
        encoding::gamma1::serialize::<GAMMA1_EXPONENT>(simd_unit, serialized)
    }
    #[inline(always)]
    fn gamma1_deserialize<const GAMMA1_EXPONENT: usize>(serialized: &[u8], out: &mut Vec256) {
        encoding::gamma1::deserialize::<GAMMA1_EXPONENT>(serialized, out);
    }

    #[inline(always)]
    fn commitment_serialize(simd_unit: &Vec256, serialized: &mut [u8]) {
        encoding::commitment::serialize(simd_unit, serialized)
    }

    #[inline(always)]
    fn error_serialize<const ETA: usize>(simd_unit: &Vec256, serialized: &mut [u8]) {
        encoding::error::serialize::<ETA>(simd_unit, serialized)
    }
    #[inline(always)]
    fn error_deserialize<const ETA: usize>(serialized: &[u8], out: &mut Self::Coefficient) {
        encoding::error::deserialize::<ETA>(serialized, out);
    }

    #[inline(always)]
    fn t0_serialize(simd_unit: &Self::Coefficient, out: &mut [u8]) {
        // out len 13
        encoding::t0::serialize(simd_unit, out);
    }
    #[inline(always)]
    fn t0_deserialize(serialized: &[u8], out: &mut Self::Coefficient) {
        encoding::t0::deserialize(serialized, out);
    }

    #[inline(always)]
    fn t1_serialize(simd_unit: &Self::Coefficient, out: &mut [u8]) {
        encoding::t1::serialize(simd_unit, out);
    }
    #[inline(always)]
    fn t1_deserialize(serialized: &[u8], out: &mut Self::Coefficient) {
        encoding::t1::deserialize(serialized, out);
    }

    #[inline(always)]
    fn ntt(simd_units: [Self; SIMD_UNITS_IN_RING_ELEMENT]) -> [Self; SIMD_UNITS_IN_RING_ELEMENT] {
        // XXX: We can't use from_fn or map here because of Eurydice.
        //      But this should be rewritten anyway to avoid having to do the map.
        //      See linked Eurydice issues in #706
        let mut re = [libcrux_intrinsics::avx2::mm256_setzero_si256(); SIMD_UNITS_IN_RING_ELEMENT];
        for i in 0..SIMD_UNITS_IN_RING_ELEMENT {
            re[i] = simd_units[i].coefficients;
        }
        let result = ntt::ntt(re);

        let mut out = [vector_type::ZERO(); SIMD_UNITS_IN_RING_ELEMENT];
        for i in 0..result.len() {
            out[i] = Self {
                coefficients: result[i],
            };
        }
        out
    }

    #[inline(always)]
    fn invert_ntt_montgomery(
        simd_units: [Self; SIMD_UNITS_IN_RING_ELEMENT],
    ) -> [Self; SIMD_UNITS_IN_RING_ELEMENT] {
        // XXX: We can't use from_fn or map here because of Eurydice.
        //      But this should be rewritten anyway to avoid having to do the map.
        let mut re = [libcrux_intrinsics::avx2::mm256_setzero_si256(); SIMD_UNITS_IN_RING_ELEMENT];
        for i in 0..SIMD_UNITS_IN_RING_ELEMENT {
            re[i] = simd_units[i].coefficients;
        }
        let result = invntt::invert_ntt_montgomery(re);

        let mut out = [vector_type::ZERO(); SIMD_UNITS_IN_RING_ELEMENT];
        for i in 0..result.len() {
            out[i] = Self {
                coefficients: result[i],
            };
        }
        out
    }
}
