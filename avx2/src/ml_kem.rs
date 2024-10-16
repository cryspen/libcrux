use super::*;
use libcrux_traits::Operations;

mod arithmetic;
mod compress;
mod ntt;
mod rej_sample_table;
mod sampling;
mod serialize;

impl Operations for SIMD256Vector {
    #[inline(always)]
    fn ZERO() -> Self {
        zero()
    }

    #[inline(always)]
    fn from_i16_array(array: &[i16]) -> Self {
        from_i16_array(array)
    }

    #[inline(always)]
    fn to_i16_array(x: Self) -> [i16; 16] {
        to_i16_array(x)
    }

    #[inline(always)]
    fn add(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: arithmetic::add(lhs.elements, rhs.elements),
        }
    }

    #[inline(always)]
    fn sub(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: arithmetic::sub(lhs.elements, rhs.elements),
        }
    }

    #[inline(always)]
    fn multiply_by_constant(v: Self, c: i16) -> Self {
        Self {
            elements: arithmetic::multiply_by_constant(v.elements, c),
        }
    }

    #[inline(always)]
    fn bitwise_and_with_constant(vector: Self, constant: i16) -> Self {
        Self {
            elements: arithmetic::bitwise_and_with_constant(vector.elements, constant),
        }
    }

    #[inline(always)]
    fn shift_right<const SHIFT_BY: i32>(vector: Self) -> Self {
        Self {
            elements: arithmetic::shift_right::<{ SHIFT_BY }>(vector.elements),
        }
    }

    #[inline(always)]
    fn cond_subtract_3329(vector: Self) -> Self {
        Self {
            elements: arithmetic::cond_subtract_3329(vector.elements),
        }
    }

    #[inline(always)]
    fn barrett_reduce(vector: Self) -> Self {
        Self {
            elements: arithmetic::barrett_reduce(vector.elements),
        }
    }

    #[inline(always)]
    fn montgomery_multiply_by_constant(vector: Self, constant: i16) -> Self {
        Self {
            elements: arithmetic::montgomery_multiply_by_constant(vector.elements, constant),
        }
    }

    #[inline(always)]
    fn compress_1(vector: Self) -> Self {
        Self {
            elements: compress::compress_message_coefficient(vector.elements),
        }
    }

    #[inline(always)]
    fn compress<const COEFFICIENT_BITS: i32>(vector: Self) -> Self {
        Self {
            elements: compress::compress_ciphertext_coefficient::<COEFFICIENT_BITS>(
                vector.elements,
            ),
        }
    }

    #[inline(always)]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(vector: Self) -> Self {
        Self {
            elements: compress::decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(
                vector.elements,
            ),
        }
    }

    #[inline(always)]
    fn ntt_layer_1_step(vector: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_1_step(vector.elements, zeta0, zeta1, zeta2, zeta3),
        }
    }

    #[inline(always)]
    fn ntt_layer_2_step(vector: Self, zeta0: i16, zeta1: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_2_step(vector.elements, zeta0, zeta1),
        }
    }

    #[inline(always)]
    fn ntt_layer_3_step(vector: Self, zeta: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_3_step(vector.elements, zeta),
        }
    }

    #[inline(always)]
    fn inv_ntt_layer_1_step(vector: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_1_step(vector.elements, zeta0, zeta1, zeta2, zeta3),
        }
    }

    #[inline(always)]
    fn inv_ntt_layer_2_step(vector: Self, zeta0: i16, zeta1: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_2_step(vector.elements, zeta0, zeta1),
        }
    }

    #[inline(always)]
    fn inv_ntt_layer_3_step(vector: Self, zeta: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_3_step(vector.elements, zeta),
        }
    }

    #[inline(always)]
    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        Self {
            elements: ntt::ntt_multiply(lhs.elements, rhs.elements, zeta0, zeta1, zeta2, zeta3),
        }
    }

    #[inline(always)]
    fn serialize_1(vector: Self) -> [u8; 2] {
        serialize::serialize_1(vector.elements)
    }

    #[inline(always)]
    fn deserialize_1(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_1(bytes),
        }
    }

    #[inline(always)]
    fn serialize_4(vector: Self) -> [u8; 8] {
        serialize::serialize_4(vector.elements)
    }

    #[inline(always)]
    fn deserialize_4(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_4(bytes),
        }
    }

    #[inline(always)]
    fn serialize_5(vector: Self) -> [u8; 10] {
        serialize::serialize_5(vector.elements)
    }

    #[inline(always)]
    fn deserialize_5(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_5(bytes),
        }
    }

    #[inline(always)]
    fn serialize_10(vector: Self) -> [u8; 20] {
        serialize::serialize_10(vector.elements)
    }

    #[inline(always)]
    fn deserialize_10(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_10(bytes),
        }
    }

    #[inline(always)]
    fn serialize_11(vector: Self) -> [u8; 22] {
        serialize::serialize_11(vector.elements)
    }

    #[inline(always)]
    fn deserialize_11(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_11(bytes),
        }
    }

    #[inline(always)]
    fn serialize_12(vector: Self) -> [u8; 24] {
        serialize::serialize_12(vector.elements)
    }

    #[inline(always)]
    fn deserialize_12(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_12(bytes),
        }
    }

    #[inline(always)]
    fn rej_sample(input: &[u8], output: &mut [i16]) -> usize {
        sampling::rejection_sample(input, output)
    }
}
