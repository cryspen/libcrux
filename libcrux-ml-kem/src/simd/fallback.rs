//use crate::hax_utils::hax_debug_assert;
use crate::{
    arithmetic::*,
    compress::{compress_ciphertext_coefficient, compress_message_coefficient},
};
//use crate::cloop;

#[derive(Clone, Copy)]
pub(crate) struct FallbackVector {
    elements: [FieldElement; 8],
}

impl crate::simd::simd_trait::Operations for FallbackVector {
    type Vector = FallbackVector;

    const FIELD_ELEMENTS_IN_VECTOR: usize = 8;

    fn ZERO() -> Self::Vector {
        Self {
            elements: [0i32; Self::FIELD_ELEMENTS_IN_VECTOR],
        }
    }

    fn to_i32_array(v: Self::Vector) -> [i32; 8] {
        v.elements
    }

    fn from_i32_array(array: [i32; 8]) -> Self::Vector {
        FallbackVector { elements: array }
    }

    fn add_constant(mut v: Self::Vector, c: i32) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            v.elements[i] += c;
        }

        v
    }
    fn add(mut lhs: Self::Vector, rhs: &Self::Vector) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            lhs.elements[i] += rhs.elements[i];
        }

        lhs
    }
    fn sub(mut lhs: Self::Vector, rhs: &Self::Vector) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            lhs.elements[i] -= rhs.elements[i];
        }

        lhs
    }

    fn multiply_by_constant(mut v: Self::Vector, c: i32) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            v.elements[i] *= c;
        }

        v
    }

    fn bitwise_and_with_constant(mut v: Self::Vector, c: i32) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            v.elements[i] &= c;
        }

        v
    }

    fn shift_right(mut v: Self::Vector, shift_amount: u8) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            v.elements[i] = v.elements[i] >> shift_amount;
        }

        v
    }

    fn shift_left(mut lhs: Self::Vector, shift_amount: u8) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            lhs.elements[i] = lhs.elements[i] << shift_amount;
        }

        lhs
    }

    fn modulo_a_constant(mut v: Self::Vector, modulus: i32) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            v.elements[i] = v.elements[i] % modulus;
        }

        v
    }

    fn barrett_reduce(mut v: Self::Vector) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            v.elements[i] = crate::arithmetic::barrett_reduce(v.elements[i]);
        }

        v
    }

    fn montgomery_reduce(mut v: Self::Vector) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            v.elements[i] = crate::arithmetic::montgomery_reduce(v.elements[i]);
        }

        v
    }

    fn compress_1(mut v: Self::Vector) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            v.elements[i] = compress_message_coefficient(v.elements[i] as u16) as i32;
        }

        v
    }

    fn compress(coefficient_bits: u8, mut v: Self::Vector) -> Self::Vector {
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            v.elements[i] =
                compress_ciphertext_coefficient(coefficient_bits, v.elements[i] as u16) as i32;
        }

        v
    }

    fn ntt_layer_1_step(mut v: Self::Vector, zeta1: i32, zeta2: i32) -> Self::Vector {
        let t = montgomery_multiply_fe_by_fer(v.elements[2], zeta1);
        v.elements[2] = v.elements[0] - t;
        v.elements[0] = v.elements[0] + t;

        let t = montgomery_multiply_fe_by_fer(v.elements[3], zeta1);
        v.elements[3] = v.elements[1] - t;
        v.elements[1] = v.elements[1] + t;

        let t = montgomery_multiply_fe_by_fer(v.elements[6], zeta2);
        v.elements[6] = v.elements[4] - t;
        v.elements[4] = v.elements[4] + t;

        let t = montgomery_multiply_fe_by_fer(v.elements[7], zeta2);
        v.elements[7] = v.elements[5] - t;
        v.elements[5] = v.elements[5] + t;

        v
    }

    fn ntt_layer_2_step(mut v: Self::Vector, zeta: i32) -> Self::Vector {
        let t = montgomery_multiply_fe_by_fer(v.elements[4], zeta);
        v.elements[4] = v.elements[0] - t;
        v.elements[0] = v.elements[0] + t;

        let t = montgomery_multiply_fe_by_fer(v.elements[5], zeta);
        v.elements[5] = v.elements[1] - t;
        v.elements[1] = v.elements[1] + t;

        let t = montgomery_multiply_fe_by_fer(v.elements[6], zeta);
        v.elements[6] = v.elements[2] - t;
        v.elements[2] = v.elements[2] + t;

        let t = montgomery_multiply_fe_by_fer(v.elements[7], zeta);
        v.elements[7] = v.elements[3] - t;
        v.elements[3] = v.elements[3] + t;

        v
    }

    fn inv_ntt_layer_1_step(mut v: Self::Vector, zeta1: i32, zeta2: i32) -> Self::Vector {
        let a_minus_b = v.elements[2] - v.elements[0];
        v.elements[0] = v.elements[0] + v.elements[2];
        v.elements[2] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

        let a_minus_b = v.elements[3] - v.elements[1];
        v.elements[1] = v.elements[1] + v.elements[3];
        v.elements[3] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

        let a_minus_b = v.elements[6] - v.elements[4];
        v.elements[4] = v.elements[4] + v.elements[6];
        v.elements[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);

        let a_minus_b = v.elements[7] - v.elements[5];
        v.elements[5] = v.elements[5] + v.elements[7];
        v.elements[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);

        v
    }

    fn inv_ntt_layer_2_step(mut v: Self::Vector, zeta: i32) -> Self::Vector {
        let a_minus_b = v.elements[4] - v.elements[0];
        v.elements[0] = v.elements[0] + v.elements[4];
        v.elements[4] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

        let a_minus_b = v.elements[5] - v.elements[1];
        v.elements[1] = v.elements[1] + v.elements[5];
        v.elements[5] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

        let a_minus_b = v.elements[6] - v.elements[2];
        v.elements[2] = v.elements[2] + v.elements[6];
        v.elements[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

        let a_minus_b = v.elements[7] - v.elements[3];
        v.elements[3] = v.elements[3] + v.elements[7];
        v.elements[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

        v
    }

    fn ntt_multiply(
        lhs: &Self::Vector,
        rhs: &Self::Vector,
        zeta0: i32,
        zeta1: i32,
    ) -> Self::Vector {
        let mut out = Self::ZERO();
        let product = ntt_multiply_binomials(
            (lhs.elements[0], lhs.elements[1]),
            (rhs.elements[0], rhs.elements[1]),
            zeta0,
        );
        out.elements[0] = product.0;
        out.elements[1] = product.1;

        let product = ntt_multiply_binomials(
            (lhs.elements[2], lhs.elements[3]),
            (rhs.elements[2], rhs.elements[3]),
            -zeta0,
        );
        out.elements[2] = product.0;
        out.elements[3] = product.1;

        let product = ntt_multiply_binomials(
            (lhs.elements[4], lhs.elements[5]),
            (rhs.elements[4], rhs.elements[5]),
            zeta1,
        );
        out.elements[4] = product.0;
        out.elements[5] = product.1;

        let product = ntt_multiply_binomials(
            (lhs.elements[6], lhs.elements[7]),
            (rhs.elements[6], rhs.elements[7]),
            -zeta1,
        );
        out.elements[6] = product.0;
        out.elements[7] = product.1;
        out
    }

    fn serialize_1(v: Self::Vector) -> u8 {
        let mut result = 0u8;
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            result |= (v.elements[i] as u8) << i;
        }

        result
    }
    fn deserialize_1(v: u8) -> Self::Vector {
        let mut result = Self::ZERO();
        for i in 0..Self::FIELD_ELEMENTS_IN_VECTOR {
            result.elements[i] = ((v >> i) & 0x1) as i32;
        }

        result
    }

    fn serialize_4(v: Self::Vector) -> [u8; 4] {
        let mut result = [0u8; 4];

        result[0] = ((v.elements[1] as u8) << 4) | (v.elements[0] as u8);
        result[1] = ((v.elements[3] as u8) << 4) | (v.elements[2] as u8);
        result[2] = ((v.elements[5] as u8) << 4) | (v.elements[4] as u8);
        result[3] = ((v.elements[7] as u8) << 4) | (v.elements[6] as u8);

        result
    }
    fn deserialize_4(bytes: &[u8]) -> Self::Vector {
        let mut v = Self::ZERO();

        v.elements[0] = (bytes[0] & 0x0F) as i32;
        v.elements[1] = ((bytes[0] >> 4) & 0x0F) as i32;

        v.elements[2] = (bytes[1] & 0x0F) as i32;
        v.elements[3] = ((bytes[1] >> 4) & 0x0F) as i32;

        v.elements[4] = (bytes[2] & 0x0F) as i32;
        v.elements[5] = ((bytes[2] >> 4) & 0x0F) as i32;

        v.elements[6] = (bytes[3] & 0x0F) as i32;
        v.elements[7] = ((bytes[3] >> 4) & 0x0F) as i32;

        v
    }

    fn serialize_5(v: Self::Vector) -> [u8; 5] {
        let mut result = [0u8; 5];

        result[0] = ((v.elements[1] & 0x7) << 5 | v.elements[0]) as u8;
        result[1] =
            (((v.elements[3] & 1) << 7) | (v.elements[2] << 2) | (v.elements[1] >> 3)) as u8;
        result[2] = (((v.elements[4] & 0xF) << 4) | (v.elements[3] >> 1)) as u8;
        result[3] =
            (((v.elements[6] & 0x3) << 6) | (v.elements[5] << 1) | (v.elements[4] >> 4)) as u8;
        result[4] = ((v.elements[7] << 3) | (v.elements[6] >> 2)) as u8;

        result
    }
    fn deserialize_5(bytes: &[u8]) -> Self::Vector {
        let mut v = Self::ZERO();

        v.elements[0] = (bytes[0] & 0x1F) as i32;
        v.elements[1] = ((bytes[1] & 0x3) << 3 | (bytes[0] >> 5)) as i32;
        v.elements[2] = ((bytes[1] >> 2) & 0x1F) as i32;
        v.elements[3] = (((bytes[2] & 0xF) << 1) | (bytes[1] >> 7)) as i32;
        v.elements[4] = (((bytes[3] & 1) << 4) | (bytes[2] >> 4)) as i32;
        v.elements[5] = ((bytes[3] >> 1) & 0x1F) as i32;
        v.elements[6] = (((bytes[4] & 0x7) << 2) | (bytes[3] >> 6)) as i32;
        v.elements[7] = (bytes[4] >> 3) as i32;

        v
    }

    fn serialize_10(v: Self::Vector) -> [u8; 10] {
        let mut result = [0u8; 10];

        result[0] = (v.elements[0] & 0xFF) as u8;
        result[1] = ((v.elements[1] & 0x3F) as u8) << 2 | ((v.elements[0] >> 8) & 0x03) as u8;
        result[2] = ((v.elements[2] & 0x0F) as u8) << 4 | ((v.elements[1] >> 6) & 0x0F) as u8;
        result[3] = ((v.elements[3] & 0x03) as u8) << 6 | ((v.elements[2] >> 4) & 0x3F) as u8;
        result[4] = ((v.elements[3] >> 2) & 0xFF) as u8;

        result[5] = (v.elements[4] & 0xFF) as u8;
        result[6] = ((v.elements[5] & 0x3F) as u8) << 2 | ((v.elements[4] >> 8) & 0x03) as u8;
        result[7] = ((v.elements[6] & 0x0F) as u8) << 4 | ((v.elements[5] >> 6) & 0x0F) as u8;
        result[8] = ((v.elements[7] & 0x03) as u8) << 6 | ((v.elements[6] >> 4) & 0x3F) as u8;
        result[9] = ((v.elements[7] >> 2) & 0xFF) as u8;

        result
    }
    fn deserialize_10(bytes: &[u8]) -> Self::Vector {
        let mut result = Self::ZERO();

        result.elements[0] = ((bytes[1] as i32 & 0x03) << 8 | (bytes[0] as i32 & 0xFF)) as i32;
        result.elements[1] = ((bytes[2] as i32 & 0x0F) << 6 | (bytes[1] as i32 >> 2)) as i32;
        result.elements[2] = ((bytes[3] as i32 & 0x3F) << 4 | (bytes[2] as i32 >> 4)) as i32;
        result.elements[3] = (((bytes[4] as i32) << 2) | (bytes[3] as i32 >> 6)) as i32;

        result.elements[4] = ((bytes[6] as i32 & 0x03) << 8 | (bytes[5] as i32 & 0xFF)) as i32;
        result.elements[5] = ((bytes[7] as i32 & 0x0F) << 6 | (bytes[6] as i32 >> 2)) as i32;
        result.elements[6] = ((bytes[8] as i32 & 0x3F) << 4 | (bytes[7] as i32 >> 4)) as i32;
        result.elements[7] = (((bytes[9] as i32) << 2) | (bytes[8] as i32 >> 6)) as i32;

        result
    }

    fn serialize_11(v: Self::Vector) -> [u8; 11] {
        let mut result = [0u8; 11];
        result[0] = v.elements[0] as u8;
        result[1] = ((v.elements[1] & 0x1F) as u8) << 3 | ((v.elements[0] >> 8) as u8);
        result[2] = ((v.elements[2] & 0x3) as u8) << 6 | ((v.elements[1] >> 5) as u8);
        result[3] = ((v.elements[2] >> 2) & 0xFF) as u8;
        result[4] = ((v.elements[3] & 0x7F) as u8) << 1 | (v.elements[2] >> 10) as u8;
        result[5] = ((v.elements[4] & 0xF) as u8) << 4 | (v.elements[3] >> 7) as u8;
        result[6] = ((v.elements[5] & 0x1) as u8) << 7 | (v.elements[4] >> 4) as u8;
        result[7] = ((v.elements[5] >> 1) & 0xFF) as u8;
        result[8] = ((v.elements[6] & 0x3F) as u8) << 2 | (v.elements[5] >> 9) as u8;
        result[9] = ((v.elements[7] & 0x7) as u8) << 5 | (v.elements[6] >> 6) as u8;
        result[10] = (v.elements[7] >> 3) as u8;
        result
    }
    fn deserialize_11(bytes: &[u8]) -> Self::Vector {
        let mut result = Self::ZERO();
        result.elements[0] = ((bytes[1] as i32 & 0x7) << 8 | bytes[0] as i32) as i32;
        result.elements[1] = ((bytes[2] as i32 & 0x3F) << 5 | (bytes[1] as i32 >> 3)) as i32;
        result.elements[2] = ((bytes[4] as i32 & 0x1) << 10
            | ((bytes[3] as i32) << 2)
            | ((bytes[2] as i32) >> 6)) as i32;
        result.elements[3] = ((bytes[5] as i32 & 0xF) << 7 | (bytes[4] as i32 >> 1)) as i32;
        result.elements[4] = ((bytes[6] as i32 & 0x7F) << 4 | (bytes[5] as i32 >> 4)) as i32;
        result.elements[5] = ((bytes[8] as i32 & 0x3) << 9
            | ((bytes[7] as i32) << 1)
            | ((bytes[6] as i32) >> 7)) as i32;
        result.elements[6] = ((bytes[9] as i32 & 0x1F) << 6 | (bytes[8] as i32 >> 2)) as i32;
        result.elements[7] = (((bytes[10] as i32) << 3) | (bytes[9] as i32 >> 5)) as i32;
        result
    }

    fn serialize_12(v: Self::Vector) -> [u8; 12] {
        let mut result = [0u8; 12];

        result[0] = (v.elements[0] & 0xFF) as u8;
        result[1] = ((v.elements[0] >> 8) | ((v.elements[1] & 0x0F) << 4)) as u8;
        result[2] = ((v.elements[1] >> 4) & 0xFF) as u8;

        result[3] = (v.elements[2] & 0xFF) as u8;
        result[4] = ((v.elements[2] >> 8) | ((v.elements[3] & 0x0F) << 4)) as u8;
        result[5] = ((v.elements[3] >> 4) & 0xFF) as u8;

        result[6] = (v.elements[4] & 0xFF) as u8;
        result[7] = ((v.elements[4] >> 8) | ((v.elements[5] & 0x0F) << 4)) as u8;
        result[8] = ((v.elements[5] >> 4) & 0xFF) as u8;

        result[9] = (v.elements[6] & 0xFF) as u8;
        result[10] = ((v.elements[6] >> 8) | ((v.elements[7] & 0x0F) << 4)) as u8;
        result[11] = ((v.elements[7] >> 4) & 0xFF) as u8;

        result
    }
    fn deserialize_12(bytes: &[u8]) -> Self::Vector {
        let mut re = Self::ZERO();

        let byte0 = bytes[0] as i32;
        let byte1 = bytes[1] as i32;
        let byte2 = bytes[2] as i32;
        let byte3 = bytes[3] as i32;
        let byte4 = bytes[4] as i32;
        let byte5 = bytes[5] as i32;
        let byte6 = bytes[6] as i32;
        let byte7 = bytes[7] as i32;
        let byte8 = bytes[8] as i32;
        let byte9 = bytes[9] as i32;
        let byte10 = bytes[10] as i32;
        let byte11 = bytes[11] as i32;

        re.elements[0] = (byte1 & 0x0F) << 8 | (byte0 & 0xFF);
        re.elements[1] = (byte2 << 4) | ((byte1 >> 4) & 0x0F);

        re.elements[2] = (byte4 & 0x0F) << 8 | (byte3 & 0xFF);
        re.elements[3] = (byte5 << 4) | ((byte4 >> 4) & 0x0F);

        re.elements[4] = (byte7 & 0x0F) << 8 | (byte6 & 0xFF);
        re.elements[5] = (byte8 << 4) | ((byte7 >> 4) & 0x0F);

        re.elements[6] = (byte10 & 0x0F) << 8 | (byte9 & 0xFF);
        re.elements[7] = (byte11 << 4) | ((byte10 >> 4) & 0x0F);

        re
    }
}
