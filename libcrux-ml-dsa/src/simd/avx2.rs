use crate::simd::traits::Operations;
use libcrux_intrinsics;

use crate::simd::portable::PortableSIMDUnit;

mod arithmetic;
mod encoding;
mod ntt;
mod rejection_sample;

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
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: Self) -> Self {
        Self {
            coefficients: arithmetic::shift_left_then_reduce::<SHIFT_BY>(simd_unit.coefficients),
        }
    }

    fn power2round(simd_unit: Self) -> (Self, Self) {
        let (lower, upper) = arithmetic::power2round(simd_unit.coefficients);

        let lower = Self {
            coefficients: lower,
        };
        let upper = Self {
            coefficients: upper,
        };

        (lower, upper)
    }

    fn infinity_norm_exceeds(simd_unit: Self, bound: i32) -> bool {
        arithmetic::infinity_norm_exceeds(simd_unit.coefficients, bound)
    }

    fn decompose<const GAMMA2: i32>(simd_unit: Self) -> (Self, Self) {
        let (lower, upper) = arithmetic::decompose::<GAMMA2>(simd_unit.coefficients);

        let lower = Self {
            coefficients: lower,
        };
        let upper = Self {
            coefficients: upper,
        };

        (lower, upper)
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
        let result = PortableSIMDUnit::gamma1_deserialize::<GAMMA1_EXPONENT>(serialized);

        Self::from_coefficient_array(&result.to_coefficient_array())
    }

    fn commitment_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::commitment::serialize::<OUTPUT_SIZE>(simd_unit.coefficients)
    }

    fn error_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE] {
        encoding::error::serialize::<OUTPUT_SIZE>(simd_unit.coefficients)
    }
    fn error_deserialize<const ETA: usize>(serialized: &[u8]) -> Self {
        AVX2SIMDUnit {
            coefficients: encoding::error::deserialize::<ETA>(serialized),
        }
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
        encoding::t1::serialize(simd_unit.coefficients)
    }
    fn t1_deserialize(serialized: &[u8]) -> Self {
        Self {
            coefficients: encoding::t1::deserialize(serialized),
        }
    }

    fn ntt_at_layer_0(simd_unit: Self, zeta0: i32, zeta1: i32, zeta2: i32, zeta3: i32) -> Self {
        Self {
            coefficients: ntt::ntt_at_layer_0(simd_unit.coefficients, zeta0, zeta1, zeta2, zeta3),
        }
    }
    fn ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self {
        Self {
            coefficients: ntt::ntt_at_layer_1(simd_unit.coefficients, zeta0, zeta1),
        }
    }
    fn ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self {
        Self {
            coefficients: ntt::ntt_at_layer_2(simd_unit.coefficients, zeta),
        }
    }

    fn invert_ntt_at_layer_0(
        simd_unit: Self,
        zeta0: i32,
        zeta1: i32,
        zeta2: i32,
        zeta3: i32,
    ) -> Self {
        Self {
            coefficients: ntt::invert_ntt_at_layer_0(
                simd_unit.coefficients,
                zeta0,
                zeta1,
                zeta2,
                zeta3,
            ),
        }
    }
    fn invert_ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self {
        Self {
            coefficients: ntt::invert_ntt_at_layer_1(simd_unit.coefficients, zeta0, zeta1),
        }
    }
    fn invert_ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self {
        Self {
            coefficients: ntt::invert_ntt_at_layer_2(simd_unit.coefficients, zeta),
        }
    }
}
