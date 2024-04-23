#![allow(dead_code)]
use crate::simd::fallback;
use core::arch::aarch64::*;

#[derive(Clone, Copy)]
pub(crate) struct SIMD128Vector {
    low: int32x4_t,
    high: int32x4_t,
}

impl crate::simd::simd_trait::Operations for SIMD128Vector {
    type Vector = SIMD128Vector;

    const FIELD_ELEMENTS_IN_VECTOR: usize = 8;

    fn ZERO() -> Self::Vector {
        SIMD128Vector {
            low: unsafe { vdupq_n_s32(0) },
            high: unsafe { vdupq_n_s32(0) },
        }
    }

    fn to_i32_array(v: Self::Vector) -> [i32; 8] {
        let mut out = [0i32; 8];

        unsafe { vst1q_s32(out[0..4].as_mut_ptr() as *mut i32, v.low) }
        unsafe { vst1q_s32(out[4..8].as_mut_ptr() as *mut i32, v.high) }

        out
    }

    fn from_i32_array(array: [i32; 8]) -> Self::Vector {
        SIMD128Vector {
            low: unsafe { vld1q_s32(array[0..4].as_ptr() as *const i32) },
            high: unsafe { vld1q_s32(array[4..8].as_ptr() as *const i32) },
        }
    }

    fn add_constant(mut v: Self::Vector, c: i32) -> Self::Vector {
        let c = unsafe { vdupq_n_s32(c) };

        v.low = unsafe { vaddq_s32(v.low, c) };
        v.high = unsafe { vaddq_s32(v.high, c) };

        v
    }

    fn add(mut lhs: Self::Vector, rhs: &Self::Vector) -> Self::Vector {
        lhs.low = unsafe { vaddq_s32(lhs.low, rhs.low) };
        lhs.high = unsafe { vaddq_s32(lhs.high, rhs.high) };
        lhs
    }

    fn sub(mut lhs: Self::Vector, rhs: &Self::Vector) -> Self::Vector {
        lhs.low = unsafe { vsubq_s32(lhs.low, rhs.low) };
        lhs.high = unsafe { vsubq_s32(lhs.high, rhs.high) };
        lhs
    }

    fn multiply_by_constant(mut v: Self::Vector, c: i32) -> Self::Vector {
        v.low = unsafe { vmulq_n_s32(v.low, c) };
        v.high = unsafe { vmulq_n_s32(v.high, c) };

        v
    }

    fn bitwise_and_with_constant(mut v: Self::Vector, c: i32) -> Self::Vector {
        let c = unsafe { vdupq_n_s32(c) };

        v.low = unsafe { vandq_s32(v.low, c) };
        v.high = unsafe { vandq_s32(v.high, c) };

        v
    }

    fn shift_right(mut v: Self::Vector, shift_amount: u8) -> Self::Vector {
        // Should find special cases of this
        // e.g when doing a right shift just to propagate signed bits, use vclezq_s32 instead
        let shift_amount = unsafe { vdupq_n_s32(-(shift_amount as i32)) };

        v.low = unsafe { vshlq_s32(v.low, shift_amount) };
        v.high = unsafe { vshlq_s32(v.high, shift_amount) };

        v
    }

    fn shift_left(mut lhs: Self::Vector, shift_amount: u8) -> Self::Vector {
        let shift_amount = unsafe { vdupq_n_s32(shift_amount as i32) };

        lhs.low = unsafe { vshlq_s32(lhs.low, shift_amount) };
        lhs.high = unsafe { vshlq_s32(lhs.high, shift_amount) };

        lhs
    }

    fn modulo_a_constant(v: Self::Vector, modulus: i32) -> Self::Vector {
        let mut i32s = Self::to_i32_array(v);

        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            i32s[i] = i32s[i] % modulus;
        }

        Self::from_i32_array(i32s)
    }

    fn barrett_reduce(v: Self::Vector) -> Self::Vector {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        let output = fallback::FallbackVector::barrett_reduce(input);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn montgomery_reduce(v: Self::Vector) -> Self::Vector {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        let output = fallback::FallbackVector::montgomery_reduce(input);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn compress_1(v: Self::Vector) -> Self::Vector {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        let output = fallback::FallbackVector::compress_1(input);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn compress(coefficient_bits: u8, v: Self::Vector) -> Self::Vector {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        let output = fallback::FallbackVector::compress(coefficient_bits, input);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn ntt_layer_1_step(v: Self::Vector, zeta1: i32, zeta2: i32) -> Self::Vector {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        let output = fallback::FallbackVector::ntt_layer_1_step(input, zeta1, zeta2);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn ntt_layer_2_step(v: Self::Vector, zeta: i32) -> Self::Vector {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        let output = fallback::FallbackVector::ntt_layer_2_step(input, zeta);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn inv_ntt_layer_1_step(v: Self::Vector, zeta1: i32, zeta2: i32) -> Self::Vector {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        let output = fallback::FallbackVector::inv_ntt_layer_1_step(input, zeta1, zeta2);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn inv_ntt_layer_2_step(v: Self::Vector, zeta: i32) -> Self::Vector {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        let output = fallback::FallbackVector::inv_ntt_layer_2_step(input, zeta);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn ntt_multiply(
        lhs: &Self::Vector,
        rhs: &Self::Vector,
        zeta0: i32,
        zeta1: i32,
    ) -> Self::Vector {
        let input1 = fallback::FallbackVector::from_i32_array(Self::to_i32_array(*lhs));
        let input2 = fallback::FallbackVector::from_i32_array(Self::to_i32_array(*rhs));

        let output = fallback::FallbackVector::ntt_multiply(&input1, &input2, zeta0, zeta1);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn serialize_1(a: Self::Vector) -> u8 {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(a));

        fallback::FallbackVector::serialize_1(input)
    }
    fn deserialize_1(a: u8) -> Self::Vector {
        let output = fallback::FallbackVector::deserialize_1(a);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn serialize_4(v: Self::Vector) -> [u8; 4] {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        fallback::FallbackVector::serialize_4(input)
    }
    fn deserialize_4(v: &[u8]) -> Self::Vector {
        let output = fallback::FallbackVector::deserialize_4(v);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn serialize_5(v: Self::Vector) -> [u8; 5] {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));

        fallback::FallbackVector::serialize_5(input)
    }
    fn deserialize_5(v: &[u8]) -> Self::Vector {
        let output = fallback::FallbackVector::deserialize_5(v);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn serialize_10(v: Self::Vector) -> [u8; 10] {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        fallback::FallbackVector::serialize_10(input)
    }
    fn deserialize_10(v: &[u8]) -> Self::Vector {
        let output = fallback::FallbackVector::deserialize_10(v);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn serialize_11(v: Self::Vector) -> [u8; 11] {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));
        fallback::FallbackVector::serialize_11(input)
    }
    fn deserialize_11(v: &[u8]) -> Self::Vector {
        let output = fallback::FallbackVector::deserialize_11(v);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }

    fn serialize_12(v: Self::Vector) -> [u8; 12] {
        let input = fallback::FallbackVector::from_i32_array(Self::to_i32_array(v));

        fallback::FallbackVector::serialize_12(input)
    }

    fn deserialize_12(v: &[u8]) -> Self::Vector {
        let output = fallback::FallbackVector::deserialize_12(v);

        Self::from_i32_array(fallback::FallbackVector::to_i32_array(output))
    }
}
