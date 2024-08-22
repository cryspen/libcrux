use super::traits::Operations;

pub(crate) use libcrux_intrinsics::avx2::*;

mod arithmetic;
mod compress;
mod ntt;
mod sampling;
mod serialize;

#[derive(Clone, Copy)]
pub struct SIMD256Vector {
    elements: Vec256,
}

#[inline(always)]
fn zero() -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_setzero_si256(),
    }
}

#[inline(always)]
fn to_i16_array(v: SIMD256Vector) -> [i16; 16] {
    let mut output = [0i16; 16];
    mm256_storeu_si256_i16(&mut output, v.elements);

    output
}

#[inline(always)]
fn from_i16_array(array: &[i16]) -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_loadu_si256_i16(array),
    }
}

impl Operations for SIMD256Vector {
    fn ZERO() -> Self {
        zero()
    }

    fn from_i16_array(array: &[i16]) -> Self {
        from_i16_array(array)
    }

    fn to_i16_array(x: Self) -> [i16; 16] {
        to_i16_array(x)
    }

    fn add(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: arithmetic::add(lhs.elements, rhs.elements),
        }
    }

    fn sub(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: arithmetic::sub(lhs.elements, rhs.elements),
        }
    }

    fn multiply_by_constant(v: Self, c: i16) -> Self {
        Self {
            elements: arithmetic::multiply_by_constant(v.elements, c),
        }
    }

    fn bitwise_and_with_constant(vector: Self, constant: i16) -> Self {
        Self {
            elements: arithmetic::bitwise_and_with_constant(vector.elements, constant),
        }
    }

    fn shift_right<const SHIFT_BY: i32>(vector: Self) -> Self {
        Self {
            elements: arithmetic::shift_right::<{ SHIFT_BY }>(vector.elements),
        }
    }

    fn cond_subtract_3329(vector: Self) -> Self {
        Self {
            elements: arithmetic::cond_subtract_3329(vector.elements),
        }
    }

    fn barrett_reduce(vector: Self) -> Self {
        Self {
            elements: arithmetic::barrett_reduce(vector.elements),
        }
    }

    fn montgomery_multiply_by_constant(vector: Self, constant: i16) -> Self {
        Self {
            elements: arithmetic::montgomery_multiply_by_constant(vector.elements, constant),
        }
    }

    fn compress_1(vector: Self) -> Self {
        Self {
            elements: compress::compress_message_coefficient(vector.elements),
        }
    }

    fn compress<const COEFFICIENT_BITS: i32>(vector: Self) -> Self {
        Self {
            elements: compress::compress_ciphertext_coefficient::<COEFFICIENT_BITS>(
                vector.elements,
            ),
        }
    }

    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(vector: Self) -> Self {
        Self {
            elements: compress::decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(
                vector.elements,
            ),
        }
    }

    fn ntt_layer_1_step(vector: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_1_step(vector.elements, zeta0, zeta1, zeta2, zeta3),
        }
    }

    fn ntt_layer_2_step(vector: Self, zeta0: i16, zeta1: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_2_step(vector.elements, zeta0, zeta1),
        }
    }

    fn ntt_layer_3_step(vector: Self, zeta: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_3_step(vector.elements, zeta),
        }
    }

    fn inv_ntt_layer_1_step(vector: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_1_step(vector.elements, zeta0, zeta1, zeta2, zeta3),
        }
    }

    fn inv_ntt_layer_2_step(vector: Self, zeta0: i16, zeta1: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_2_step(vector.elements, zeta0, zeta1),
        }
    }

    fn inv_ntt_layer_3_step(vector: Self, zeta: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_3_step(vector.elements, zeta),
        }
    }

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

    fn serialize_1(vector: Self) -> [u8; 2] {
        serialize::serialize_1(vector.elements)
    }

    fn deserialize_1(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_1(bytes),
        }
    }

    fn serialize_4(vector: Self) -> [u8; 8] {
        serialize::serialize_4(vector.elements)
    }

    fn deserialize_4(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_4(bytes),
        }
    }

    fn serialize_5(vector: Self) -> [u8; 10] {
        serialize::serialize_5(vector.elements)
    }

    fn deserialize_5(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_5(bytes),
        }
    }

    fn serialize_10(vector: Self) -> [u8; 20] {
        serialize::serialize_10(vector.elements)
    }

    fn deserialize_10(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_10(bytes),
        }
    }

    fn serialize_11(vector: Self) -> [u8; 22] {
        serialize::serialize_11(vector.elements)
    }

    fn deserialize_11(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_11(bytes),
        }
    }

    fn serialize_12(vector: Self) -> [u8; 24] {
        serialize::serialize_12(vector.elements)
    }

    fn deserialize_12(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_12(bytes),
        }
    }

    fn rej_sample(input: &[u8], output: &mut [i16]) -> usize {
        sampling::rejection_sample(input, output)
    }
}
