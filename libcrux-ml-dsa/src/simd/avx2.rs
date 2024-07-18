use crate::simd::traits::Operations;
use libcrux_intrinsics;

use crate::simd::portable::PortableSIMDUnit;

mod arithmetic;

#[derive(Clone, Copy)]
pub struct AVX2SIMDUnit {
    pub(crate) coefficients: libcrux_intrinsics::avx2::Vec256,
}

impl Operations for AVX2SIMDUnit {
    fn ZERO() -> Self {
        Self {
            coefficients: libcrux_intrinsics::avx2::mm256_setzero_si256(),
        }
    }

    fn from_coefficient_array(coefficient_array: &[i32]) -> Self {
        Self {
            coefficients: libcrux_intrinsics::avx2::mm256_loadu_si256_i32(coefficient_array),
        }
    }

    fn to_coefficient_array(&self) -> [i32; 8] {
        let mut coefficient_array = [0i32; 8];
        libcrux_intrinsics::avx2::mm256_storeu_si256_i32(&mut coefficient_array, self.coefficients);

        coefficient_array
    }

    fn add(lhs: &Self, rhs: &Self) -> Self {
        Self {
            coefficients: arithmetic::add(lhs.coefficients, rhs.coefficients),
        }
    }

    fn subtract(lhs: &Self, rhs: &Self) -> Self {
        Self {
            coefficients: arithmetic::subtract(lhs.coefficients, rhs.coefficients),
        }
    }

    fn montgomery_multiply_by_constant(simd_unit: Self, constant: i32) -> Self {
        Self {
            coefficients: arithmetic::montgomery_multiply_by_constant(
                simd_unit.coefficients,
                constant,
            ),
        }
    }
    fn montgomery_multiply(lhs: Self, rhs: Self) -> Self {
        Self {
            coefficients: arithmetic::montgomery_multiply(lhs.coefficients, rhs.coefficients),
        }
    }
    fn shift_left_then_reduce(simd_unit: Self, shift_by: usize) -> Self {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        let result = PortableSIMDUnit::shift_left_then_reduce(simd_unit, shift_by);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }

    fn power2round(simd_unit: Self) -> (Self, Self) {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        let (lower, upper) = PortableSIMDUnit::power2round(simd_unit);

        (
            Self::from_coefficient_array(&lower.to_coefficient_array()),
            Self::from_coefficient_array(&upper.to_coefficient_array()),
        )
    }

    fn infinity_norm_exceeds(simd_unit: Self, bound: i32) -> bool {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        PortableSIMDUnit::infinity_norm_exceeds(simd_unit, bound)
    }

    fn decompose<const GAMMA2: i32>(simd_unit: Self) -> (Self, Self) {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        let (lower, upper) = PortableSIMDUnit::decompose::<GAMMA2>(simd_unit);

        (
            Self::from_coefficient_array(&lower.to_coefficient_array()),
            Self::from_coefficient_array(&upper.to_coefficient_array()),
        )
    }

    fn compute_hint<const GAMMA2: i32>(low: Self, high: Self) -> (usize, Self) {
        let low = PortableSIMDUnit::from_coefficient_array(&low.to_coefficient_array());
        let high = PortableSIMDUnit::from_coefficient_array(&high.to_coefficient_array());

        let (count, hint) = PortableSIMDUnit::compute_hint::<GAMMA2>(low, high);

        (
            count,
            Self::from_coefficient_array(&hint.to_coefficient_array()),
        )
    }
    fn use_hint<const GAMMA2: i32>(simd_unit: Self, hint: Self) -> Self {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());
        let hint = PortableSIMDUnit::from_coefficient_array(&hint.to_coefficient_array());

        let result = PortableSIMDUnit::use_hint::<GAMMA2>(simd_unit, hint);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }

    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
        PortableSIMDUnit::rejection_sample_less_than_field_modulus(randomness, out)
    }
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
        PortableSIMDUnit::rejection_sample_less_than_eta_equals_2(randomness, out)
    }
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
        PortableSIMDUnit::rejection_sample_less_than_eta_equals_4(randomness, out)
    }

    fn gamma1_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        PortableSIMDUnit::gamma1_serialize::<OUTPUT_SIZE>(simd_unit)
    }
    fn gamma1_deserialize<const GAMMA1_EXPONENT: usize>(serialized: &[u8]) -> Self {
        let result = PortableSIMDUnit::gamma1_deserialize::<GAMMA1_EXPONENT>(serialized);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }

    fn commitment_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        PortableSIMDUnit::commitment_serialize::<{ OUTPUT_SIZE }>(simd_unit)
    }

    fn error_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        PortableSIMDUnit::error_serialize(simd_unit)
    }
    fn error_deserialize<const ETA: usize>(serialized: &[u8]) -> Self {
        let result = PortableSIMDUnit::error_deserialize::<{ ETA }>(serialized);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }

    fn t0_serialize(simd_unit: Self) -> [u8; 13] {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        PortableSIMDUnit::t0_serialize(simd_unit)
    }
    fn t0_deserialize(serialized: &[u8]) -> Self {
        let result = PortableSIMDUnit::t0_deserialize(serialized);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }

    fn t1_serialize(simd_unit: Self) -> [u8; 10] {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        PortableSIMDUnit::t1_serialize(simd_unit)
    }
    fn t1_deserialize(serialized: &[u8]) -> Self {
        let result = PortableSIMDUnit::t1_deserialize(serialized);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }

    fn ntt_at_layer_0(simd_unit: Self, zeta0: i32, zeta1: i32, zeta2: i32, zeta3: i32) -> Self {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        let result = PortableSIMDUnit::ntt_at_layer_0(simd_unit, zeta0, zeta1, zeta2, zeta3);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }
    fn ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        let result = PortableSIMDUnit::ntt_at_layer_1(simd_unit, zeta0, zeta1);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }
    fn ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        let result = PortableSIMDUnit::ntt_at_layer_2(simd_unit, zeta);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }

    fn invert_ntt_at_layer_0(
        simd_unit: Self,
        zeta0: i32,
        zeta1: i32,
        zeta2: i32,
        zeta3: i32,
    ) -> Self {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        let result = PortableSIMDUnit::invert_ntt_at_layer_0(simd_unit, zeta0, zeta1, zeta2, zeta3);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }
    fn invert_ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        let result = PortableSIMDUnit::invert_ntt_at_layer_1(simd_unit, zeta0, zeta1);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }
    fn invert_ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self {
        let simd_unit = PortableSIMDUnit::from_coefficient_array(&simd_unit.to_coefficient_array());

        let result = PortableSIMDUnit::invert_ntt_at_layer_2(simd_unit, zeta);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }
}
