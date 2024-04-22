//use crate::hax_utils::hax_debug_assert;
use crate::{
    arithmetic::*,
    compress::{compress_ciphertext_coefficient, compress_message_coefficient},
};
//use crate::cloop;

pub(crate) const SIZE_VEC: usize = 8;

#[derive(Clone, Copy)]
pub(crate) struct IntVec {
    elements: [FieldElement; 8],
}

/// BASIC INTEGER OPERATIONS

// Eventually, this should only be used for debugging
// In the meantime, it allows us to convert between different vector representations
#[inline(always)]
pub(crate) fn to_i32_array(a: IntVec) -> [i32; 8] {
    a.elements
}

// This function is used in sampling (until we figure out how to vectorize it)
// Eventually, this should only be used for debugging
// In the meantime, it allows us to convert between different vector representations
#[inline(always)]
pub(crate) fn from_i32_array(a: [i32; 8]) -> IntVec {
    IntVec { elements: a }
}

pub(crate) const fn ZERO_VEC() -> IntVec {
    IntVec {
        elements: [0i32; 8],
    }
}

// Basic addition with a constant
#[inline(always)]
pub(crate) fn add_constant(mut lhs: IntVec, rhs: i32) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] += rhs;
    }
    lhs
}

// Basic addition
#[inline(always)]
pub(crate) fn add(mut lhs: IntVec, rhs: &IntVec) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] += rhs.elements[i];
    }
    lhs
}

// Basic subtraction
#[inline(always)]
pub(crate) fn sub(mut lhs: IntVec, rhs: &IntVec) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] -= rhs.elements[i];
    }
    lhs
}

// Basic multiplication with constant
#[inline(always)]
pub(crate) fn mul_constant(mut lhs: IntVec, rhs: i32) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] *= rhs;
    }
    lhs
}

// Basic multiplication with constant
#[inline(always)]
pub(crate) fn bit_and_constant(mut lhs: IntVec, rhs: i32) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] &= rhs;
    }
    lhs
}

// Basic arithmetic shift right
#[inline(always)]
pub(crate) fn right_shift(mut lhs: IntVec, rhs: u8) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] = lhs.elements[i] >> rhs;
    }
    lhs
}

// Basic shift left
#[inline(always)]
pub(crate) fn left_shift(mut lhs: IntVec, rhs: u8) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] = lhs.elements[i] << rhs;
    }
    lhs
}

// Basic modulus
#[inline(always)]
pub(crate) fn modulus_constant_var_time(mut lhs: IntVec, rhs: i32) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] = lhs.elements[i] % rhs;
    }
    lhs
}

/// Arithmetic and serialization unctions that need specialized implementations

// Barrett: needs specialized implementation since i32 gets multiplied to obtain intermediate i64
#[inline(always)]
pub(crate) fn barrett_reduce(mut a: IntVec) -> IntVec {
    for i in 0..SIZE_VEC {
        a.elements[i] = crate::arithmetic::barrett_reduce(a.elements[i]);
    }
    a
}

// Montgomery: mostly generic but uses a u32->i16->i32 conversion that may need specialized treatment
#[inline(always)]
pub(crate) fn montgomery_reduce(mut a: IntVec) -> IntVec {
    for i in 0..SIZE_VEC {
        a.elements[i] = crate::arithmetic::montgomery_reduce(a.elements[i]);
    }
    a
}

// Compress Message Coefficient: mostly generic but uses some i16 arithmetic
#[inline(always)]
pub(crate) fn compress_1(mut a: IntVec) -> IntVec {
    for i in 0..SIZE_VEC {
        a.elements[i] = compress_message_coefficient(a.elements[i] as u16) as i32;
    }
    a
}

// Compress Ciphertext Coefficient: mostly generic but uses some i64 arithmetic
#[inline(always)]
pub(crate) fn compress(coefficient_bits: u8, mut a: IntVec) -> IntVec {
    for i in 0..SIZE_VEC {
        a.elements[i] =
            compress_ciphertext_coefficient(coefficient_bits, a.elements[i] as u16) as i32;
    }
    a
}

/// NTT
///
#[inline(always)]
pub(crate) fn ntt_layer_1_step(mut a: IntVec, zeta1: i32, zeta2: i32) -> IntVec {
    let t = montgomery_multiply_fe_by_fer(a.elements[2], zeta1);
    a.elements[2] = a.elements[0] - t;
    a.elements[0] = a.elements[0] + t;

    let t = montgomery_multiply_fe_by_fer(a.elements[3], zeta1);
    a.elements[3] = a.elements[1] - t;
    a.elements[1] = a.elements[1] + t;

    let t = montgomery_multiply_fe_by_fer(a.elements[6], zeta2);
    a.elements[6] = a.elements[4] - t;
    a.elements[4] = a.elements[4] + t;

    let t = montgomery_multiply_fe_by_fer(a.elements[7], zeta2);
    a.elements[7] = a.elements[5] - t;
    a.elements[5] = a.elements[5] + t;

    a
}

#[inline(always)]
pub(crate) fn ntt_layer_2_step(mut a: IntVec, zeta: i32) -> IntVec {
    let t = montgomery_multiply_fe_by_fer(a.elements[4], zeta);
    a.elements[4] = a.elements[0] - t;
    a.elements[0] = a.elements[0] + t;

    let t = montgomery_multiply_fe_by_fer(a.elements[5], zeta);
    a.elements[5] = a.elements[1] - t;
    a.elements[1] = a.elements[1] + t;

    let t = montgomery_multiply_fe_by_fer(a.elements[6], zeta);
    a.elements[6] = a.elements[2] - t;
    a.elements[2] = a.elements[2] + t;

    let t = montgomery_multiply_fe_by_fer(a.elements[7], zeta);
    a.elements[7] = a.elements[3] - t;
    a.elements[3] = a.elements[3] + t;

    a
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_1_step(mut a: IntVec, zeta1: i32, zeta2: i32) -> IntVec {
    let a_minus_b = a.elements[2] - a.elements[0];
    a.elements[0] = a.elements[0] + a.elements[2];
    a.elements[2] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = a.elements[3] - a.elements[1];
    a.elements[1] = a.elements[1] + a.elements[3];
    a.elements[3] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = a.elements[6] - a.elements[4];
    a.elements[4] = a.elements[4] + a.elements[6];
    a.elements[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);

    let a_minus_b = a.elements[7] - a.elements[5];
    a.elements[5] = a.elements[5] + a.elements[7];
    a.elements[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);
    a
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_step(mut a: IntVec, zeta: i32) -> IntVec {
    let a_minus_b = a.elements[4] - a.elements[0];
    a.elements[0] = a.elements[0] + a.elements[4];
    a.elements[4] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = a.elements[5] - a.elements[1];
    a.elements[1] = a.elements[1] + a.elements[5];
    a.elements[5] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = a.elements[6] - a.elements[2];
    a.elements[2] = a.elements[2] + a.elements[6];
    a.elements[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = a.elements[7] - a.elements[3];
    a.elements[3] = a.elements[3] + a.elements[7];
    a.elements[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);
    a
}

#[inline(always)]
pub(crate) fn ntt_multiply(lhs: &IntVec, rhs: &IntVec, zeta0: i32, zeta1: i32) -> IntVec {
    let mut out = ZERO_VEC;
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

/// SERIALIZE - DESERIALIZE
///
#[inline(always)]
pub(crate) fn serialize_1(a: IntVec) -> u8 {
    let mut result = 0u8;
    for i in 0..SIZE_VEC {
        result |= (a.elements[i] as u8) << i;
    }
    result
}

#[inline(always)]
pub(crate) fn deserialize_1(a: u8) -> IntVec {
    let mut result = ZERO_VEC;
    for i in 0..SIZE_VEC {
        result.elements[i] = ((a >> i) & 0x1) as i32;
    }
    result
}

#[inline(always)]
pub(crate) fn serialize_5(a: IntVec) -> [u8; 5] {
    let mut result = [0u8; 5];
    result[0] = ((a.elements[1] & 0x7) << 5 | a.elements[0]) as u8;
    result[1] = (((a.elements[3] & 1) << 7) | (a.elements[2] << 2) | (a.elements[1] >> 3)) as u8;
    result[2] = (((a.elements[4] & 0xF) << 4) | (a.elements[3] >> 1)) as u8;
    result[3] = (((a.elements[6] & 0x3) << 6) | (a.elements[5] << 1) | (a.elements[4] >> 4)) as u8;
    result[4] = ((a.elements[7] << 3) | (a.elements[6] >> 2)) as u8;
    result
}

#[inline(always)]
pub(crate) fn deserialize_5(bytes: &[u8]) -> IntVec {
    let mut a = ZERO_VEC;
    a.elements[0] = (bytes[0] & 0x1F) as i32;
    a.elements[1] = ((bytes[1] & 0x3) << 3 | (bytes[0] >> 5)) as i32;
    a.elements[2] = ((bytes[1] >> 2) & 0x1F) as i32;
    a.elements[3] = (((bytes[2] & 0xF) << 1) | (bytes[1] >> 7)) as i32;
    a.elements[4] = (((bytes[3] & 1) << 4) | (bytes[2] >> 4)) as i32;
    a.elements[5] = ((bytes[3] >> 1) & 0x1F) as i32;
    a.elements[6] = (((bytes[4] & 0x7) << 2) | (bytes[3] >> 6)) as i32;
    a.elements[7] = (bytes[4] >> 3) as i32;
    a
}

#[inline(always)]
pub(crate) fn serialize_4(a: IntVec) -> [u8; 4] {
    let mut result = [0u8; 4];

    result[0] = ((a.elements[1] as u8) << 4) | (a.elements[0] as u8);
    result[1] = ((a.elements[3] as u8) << 4) | (a.elements[2] as u8);
    result[2] = ((a.elements[5] as u8) << 4) | (a.elements[4] as u8);
    result[3] = ((a.elements[7] as u8) << 4) | (a.elements[6] as u8);

    result
}

#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[u8]) -> IntVec {
    let mut a = ZERO_VEC;
    a.elements[0] = (bytes[0] & 0x0F) as i32;
    a.elements[1] = ((bytes[0] >> 4) & 0x0F) as i32;

    a.elements[2] = (bytes[1] & 0x0F) as i32;
    a.elements[3] = ((bytes[1] >> 4) & 0x0F) as i32;

    a.elements[4] = (bytes[2] & 0x0F) as i32;
    a.elements[5] = ((bytes[2] >> 4) & 0x0F) as i32;

    a.elements[6] = (bytes[3] & 0x0F) as i32;
    a.elements[7] = ((bytes[3] >> 4) & 0x0F) as i32;

    a
}

#[inline(always)]
pub(crate) fn serialize_10(a: IntVec) -> [u8; 10] {
    let mut result = [0u8; 10];

    result[0] = (a.elements[0] & 0xFF) as u8;
    result[1] = ((a.elements[1] & 0x3F) as u8) << 2 | ((a.elements[0] >> 8) & 0x03) as u8;
    result[2] = ((a.elements[2] & 0x0F) as u8) << 4 | ((a.elements[1] >> 6) & 0x0F) as u8;
    result[3] = ((a.elements[3] & 0x03) as u8) << 6 | ((a.elements[2] >> 4) & 0x3F) as u8;
    result[4] = ((a.elements[3] >> 2) & 0xFF) as u8;

    result[5] = (a.elements[4] & 0xFF) as u8;
    result[6] = ((a.elements[5] & 0x3F) as u8) << 2 | ((a.elements[4] >> 8) & 0x03) as u8;
    result[7] = ((a.elements[6] & 0x0F) as u8) << 4 | ((a.elements[5] >> 6) & 0x0F) as u8;
    result[8] = ((a.elements[7] & 0x03) as u8) << 6 | ((a.elements[6] >> 4) & 0x3F) as u8;
    result[9] = ((a.elements[7] >> 2) & 0xFF) as u8;

    result
}

#[inline(always)]
pub(crate) fn deserialize_10(bytes: &[u8]) -> IntVec {
    let mut result = ZERO_VEC;

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

#[inline(always)]
pub(crate) fn serialize_11(a: IntVec) -> [u8; 11] {
    let mut result = [0u8; 11];
    result[0] = a.elements[0] as u8;
    result[1] = ((a.elements[1] & 0x1F) as u8) << 3 | ((a.elements[0] >> 8) as u8);
    result[2] = ((a.elements[2] & 0x3) as u8) << 6 | ((a.elements[1] >> 5) as u8);
    result[3] = ((a.elements[2] >> 2) & 0xFF) as u8;
    result[4] = ((a.elements[3] & 0x7F) as u8) << 1 | (a.elements[2] >> 10) as u8;
    result[5] = ((a.elements[4] & 0xF) as u8) << 4 | (a.elements[3] >> 7) as u8;
    result[6] = ((a.elements[5] & 0x1) as u8) << 7 | (a.elements[4] >> 4) as u8;
    result[7] = ((a.elements[5] >> 1) & 0xFF) as u8;
    result[8] = ((a.elements[6] & 0x3F) as u8) << 2 | (a.elements[5] >> 9) as u8;
    result[9] = ((a.elements[7] & 0x7) as u8) << 5 | (a.elements[6] >> 6) as u8;
    result[10] = (a.elements[7] >> 3) as u8;
    result
}

#[inline(always)]
pub(crate) fn deserialize_11(bytes: &[u8]) -> IntVec {
    let mut result = ZERO_VEC;
    result.elements[0] = ((bytes[1] as i32 & 0x7) << 8 | bytes[0] as i32) as i32;
    result.elements[1] = ((bytes[2] as i32 & 0x3F) << 5 | (bytes[1] as i32 >> 3)) as i32;
    result.elements[2] = ((bytes[4] as i32 & 0x1) << 10
        | ((bytes[3] as i32) << 2)
        | ((bytes[2] as i32) >> 6)) as i32;
    result.elements[3] = ((bytes[5] as i32 & 0xF) << 7 | (bytes[4] as i32 >> 1)) as i32;
    result.elements[4] = ((bytes[6] as i32 & 0x7F) << 4 | (bytes[5] as i32 >> 4)) as i32;
    result.elements[5] =
        ((bytes[8] as i32 & 0x3) << 9 | ((bytes[7] as i32) << 1) | ((bytes[6] as i32) >> 7)) as i32;
    result.elements[6] = ((bytes[9] as i32 & 0x1F) << 6 | (bytes[8] as i32 >> 2)) as i32;
    result.elements[7] = (((bytes[10] as i32) << 3) | (bytes[9] as i32 >> 5)) as i32;
    result
}

#[inline(always)]
pub(crate) fn serialize_12(a: IntVec) -> [u8; 12] {
    let mut result = [0u8; 12];

    result[0] = (a.elements[0] & 0xFF) as u8;
    result[1] = ((a.elements[0] >> 8) | ((a.elements[1] & 0x0F) << 4)) as u8;
    result[2] = ((a.elements[1] >> 4) & 0xFF) as u8;

    result[3] = (a.elements[2] & 0xFF) as u8;
    result[4] = ((a.elements[2] >> 8) | ((a.elements[3] & 0x0F) << 4)) as u8;
    result[5] = ((a.elements[3] >> 4) & 0xFF) as u8;

    result[6] = (a.elements[4] & 0xFF) as u8;
    result[7] = ((a.elements[4] >> 8) | ((a.elements[5] & 0x0F) << 4)) as u8;
    result[8] = ((a.elements[5] >> 4) & 0xFF) as u8;

    result[9] = (a.elements[6] & 0xFF) as u8;
    result[10] = ((a.elements[6] >> 8) | ((a.elements[7] & 0x0F) << 4)) as u8;
    result[11] = ((a.elements[7] >> 4) & 0xFF) as u8;

    result
}

#[inline(always)]
pub(crate) fn deserialize_12(bytes: &[u8]) -> IntVec {
    let mut re = ZERO_VEC;
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
