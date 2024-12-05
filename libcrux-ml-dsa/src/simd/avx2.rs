use crate::simd::traits::{Operations, SIMD_UNITS_IN_RING_ELEMENT};

mod arithmetic;
mod encoding;
mod invntt;
mod ntt;
mod rejection_sample;
mod vector_type;

pub(crate) use vector_type::AVX2SIMDUnit;

impl Operations for AVX2SIMDUnit {
    #[inline(always)]
    fn ZERO() -> Self {
        vector_type::ZERO()
    }

    #[inline(always)]
    fn from_coefficient_array(coefficient_array: &[i32]) -> Self {
        vector_type::from_coefficient_array(coefficient_array)
    }

    #[inline(always)]
    fn to_coefficient_array(&self) -> [i32; 8] {
        vector_type::to_coefficient_array(&self)
    }
    #[inline(always)]
    fn add(lhs: &Self, rhs: &Self) -> Self {
        arithmetic::add(lhs.coefficients, rhs.coefficients).into()
    }
    #[inline(always)]
    fn subtract(lhs: &Self, rhs: &Self) -> Self {
        arithmetic::subtract(lhs.coefficients, rhs.coefficients).into()
    }

    #[inline(always)]
    fn montgomery_multiply(lhs: Self, rhs: Self) -> Self {
        arithmetic::montgomery_multiply(lhs.coefficients, rhs.coefficients).into()
    }
    #[inline(always)]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: Self) -> Self {
        arithmetic::shift_left_then_reduce::<SHIFT_BY>(simd_unit.coefficients).into()
    }

    #[inline(always)]
    fn power2round(simd_unit: Self) -> (Self, Self) {
        let (lower, upper) = arithmetic::power2round(simd_unit.coefficients);

        (lower.into(), upper.into())
    }

    #[inline(always)]
    fn infinity_norm_exceeds(simd_unit: Self, bound: i32) -> bool {
        arithmetic::infinity_norm_exceeds(simd_unit.coefficients, bound)
    }

    #[inline(always)]
    fn decompose<const GAMMA2: i32>(simd_unit: Self) -> (Self, Self) {
        let (lower, upper) = arithmetic::decompose::<GAMMA2>(simd_unit.coefficients);

        (lower.into(), upper.into())
    }

    #[inline(always)]
    fn compute_hint<const GAMMA2: i32>(low: Self, high: Self) -> (usize, Self) {
        let (count, hint) = arithmetic::compute_hint::<GAMMA2>(low.coefficients, high.coefficients);

        (count, hint.into())
    }
    #[inline(always)]
    fn use_hint<const GAMMA2: i32>(simd_unit: Self, hint: Self) -> Self {
        arithmetic::use_hint::<GAMMA2>(simd_unit.coefficients, hint.coefficients).into()
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
    fn gamma1_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::gamma1::serialize::<OUTPUT_SIZE>(simd_unit.coefficients)
    }
    #[inline(always)]
    fn gamma1_deserialize<const GAMMA1_EXPONENT: usize>(serialized: &[u8]) -> Self {
        encoding::gamma1::deserialize::<GAMMA1_EXPONENT>(serialized).into()
    }

    #[inline(always)]
    fn commitment_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::commitment::serialize::<OUTPUT_SIZE>(simd_unit.coefficients)
    }

    #[inline(always)]
    fn error_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::error::serialize::<OUTPUT_SIZE>(simd_unit.coefficients)
    }
    #[inline(always)]
    fn error_deserialize<const ETA: usize>(serialized: &[u8]) -> Self {
        encoding::error::deserialize::<ETA>(serialized).into()
    }

    #[inline(always)]
    fn t0_serialize(simd_unit: Self) -> [u8; 13] {
        encoding::t0::serialize(simd_unit.coefficients)
    }
    #[inline(always)]
    fn t0_deserialize(serialized: &[u8]) -> Self {
        encoding::t0::deserialize(serialized).into()
    }

    #[inline(always)]
    fn t1_serialize(simd_unit: Self) -> [u8; 10] {
        encoding::t1::serialize(simd_unit.coefficients)
    }
    #[inline(always)]
    fn t1_deserialize(serialized: &[u8]) -> Self {
        encoding::t1::deserialize(serialized).into()
    }

    #[inline(always)]
    fn ntt(simd_units: [Self; SIMD_UNITS_IN_RING_ELEMENT]) -> [Self; SIMD_UNITS_IN_RING_ELEMENT] {
        // XXX: We can't use from_fn or map here because of Eurydice.
        //      But this should be rewritten anyway to avoid having to do the map.
        let mut re = [libcrux_intrinsics::avx2::mm256_setzero_si256(); SIMD_UNITS_IN_RING_ELEMENT];
        for i in 0..SIMD_UNITS_IN_RING_ELEMENT {
            re[i] = simd_units[i].coefficients;
        }
        let result = ntt::ntt(re);

        core::array::from_fn(|i| Self {
            coefficients: result[i],
        })
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

        core::array::from_fn(|i| Self {
            coefficients: result[i],
        })
    }
}
