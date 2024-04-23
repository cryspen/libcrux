#![allow(dead_code)]
use crate::simd::portable;
use core::arch::x86_64::*;

#[derive(Clone, Copy)]
pub(crate) struct SIMD256Vector {
    elements: __m256i,
}

impl crate::simd::simd_trait::Operations for SIMD256Vector {
    type Vector = Self;

    const FIELD_ELEMENTS_IN_VECTOR: usize = 8;

    fn ZERO() -> Self::Vector {
        Self {
            elements: unsafe { _mm256_setzero_si256() },
        }
    }

    fn to_i32_array(v: Self::Vector) -> [i32; 8] {
        let mut out = [0i32; 8];

        unsafe {
            _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, v.elements);
        }

        out
    }

    fn from_i32_array(array: [i32; 8]) -> Self::Vector {
        SIMD256Vector {
            elements: unsafe { _mm256_loadu_si256(array.as_ptr() as *const __m256i) },
        }
    }

    fn add_constant(mut v: Self::Vector, c: i32) -> Self::Vector {
        let c = unsafe { _mm256_set_epi32(c, c, c, c, c, c, c, c) };

        v.elements = unsafe { _mm256_add_epi32(v.elements, c) };

        v
    }
    fn add(mut lhs: Self::Vector, rhs: &Self::Vector) -> Self::Vector {
        lhs.elements = unsafe { _mm256_add_epi32(lhs.elements, rhs.elements) };

        lhs
    }

    fn sub(mut lhs: Self::Vector, rhs: &Self::Vector) -> Self::Vector {
        lhs.elements = unsafe { _mm256_sub_epi32(lhs.elements, rhs.elements) };

        lhs
    }

    fn multiply_by_constant(v: Self::Vector, c: i32) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::multiply_by_constant(input, c);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn bitwise_and_with_constant(mut v: Self::Vector, c: i32) -> Self::Vector {
        let c = unsafe { _mm256_set_epi32(c, c, c, c, c, c, c, c) };

        v.elements = unsafe { _mm256_and_si256(v.elements, c) };

        v
    }

    fn shift_right(v: Self::Vector, shift_by: u8) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::shift_right(input, shift_by);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn shift_left(v: Self::Vector, shift_by: u8) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::shift_left(input, shift_by);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn modulo_a_constant(v: Self::Vector, modulus: i32) -> Self::Vector {
        let mut i32s = Self::to_i32_array(v);

        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            i32s[i] = i32s[i] % modulus;
        }

        Self::from_i32_array(i32s)
    }

    fn barrett_reduce(v: Self::Vector) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::barrett_reduce(input);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn montgomery_reduce(v: Self::Vector) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::montgomery_reduce(input);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn compress_1(v: Self::Vector) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::compress_1(input);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn compress(coefficient_bits: u8, v: Self::Vector) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::compress(coefficient_bits, input);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn ntt_layer_1_step(v: Self::Vector, zeta1: i32, zeta2: i32) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::ntt_layer_1_step(input, zeta1, zeta2);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn ntt_layer_2_step(v: Self::Vector, zeta: i32) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::ntt_layer_2_step(input, zeta);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn inv_ntt_layer_1_step(v: Self::Vector, zeta1: i32, zeta2: i32) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::inv_ntt_layer_1_step(input, zeta1, zeta2);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn inv_ntt_layer_2_step(v: Self::Vector, zeta: i32) -> Self::Vector {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::inv_ntt_layer_2_step(input, zeta);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn ntt_multiply(
        lhs: &Self::Vector,
        rhs: &Self::Vector,
        zeta0: i32,
        zeta1: i32,
    ) -> Self::Vector {
        let input1 = portable::PortableVector::from_i32_array(Self::to_i32_array(*lhs));
        let input2 = portable::PortableVector::from_i32_array(Self::to_i32_array(*rhs));

        let output = portable::PortableVector::ntt_multiply(&input1, &input2, zeta0, zeta1);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn serialize_1(a: Self::Vector) -> u8 {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(a));

        portable::PortableVector::serialize_1(input)
    }
    fn deserialize_1(a: u8) -> Self::Vector {
        let output = portable::PortableVector::deserialize_1(a);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn serialize_4(v: Self::Vector) -> [u8; 4] {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        portable::PortableVector::serialize_4(input)
    }
    fn deserialize_4(v: &[u8]) -> Self::Vector {
        let output = portable::PortableVector::deserialize_4(v);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn serialize_5(v: Self::Vector) -> [u8; 5] {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));

        portable::PortableVector::serialize_5(input)
    }
    fn deserialize_5(v: &[u8]) -> Self::Vector {
        let output = portable::PortableVector::deserialize_5(v);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn serialize_10(v: Self::Vector) -> [u8; 10] {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        portable::PortableVector::serialize_10(input)
    }
    fn deserialize_10(v: &[u8]) -> Self::Vector {
        let output = portable::PortableVector::deserialize_10(v);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn serialize_11(v: Self::Vector) -> [u8; 11] {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        portable::PortableVector::serialize_11(input)
    }
    fn deserialize_11(v: &[u8]) -> Self::Vector {
        let output = portable::PortableVector::deserialize_11(v);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn serialize_12(v: Self::Vector) -> [u8; 12] {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));

        portable::PortableVector::serialize_12(input)
    }

    fn deserialize_12(v: &[u8]) -> Self::Vector {
        let output = portable::PortableVector::deserialize_12(v);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }
}
