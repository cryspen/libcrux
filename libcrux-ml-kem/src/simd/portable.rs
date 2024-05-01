use crate::{
    arithmetic::*,
    compress::{compress_ciphertext_coefficient, compress_message_coefficient},
    simd::simd_trait::*,
};

// #[derive(Clone, Copy)]
// pub(crate) struct PortableVector {
//     elements: [FieldElement; 8],
// }

pub(crate) type PortableVector = [FieldElement; 8];

#[allow(non_snake_case)]
#[inline(always)]
fn ZERO() -> PortableVector {
   [0i32; FIELD_ELEMENTS_IN_VECTOR]
}

#[inline(always)]
fn to_i32_array(v: PortableVector) -> [i32; 8] {
    v
}

#[inline(always)]
fn from_i32_array(array: [i32; 8]) -> PortableVector {
    array
}

#[inline(always)]
fn add_constant(mut v: PortableVector, c: i32) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v[i] += c;
    }

    v
}

#[inline(always)]
fn add(mut lhs: PortableVector, rhs: &PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs[i] += rhs[i];
    }

    lhs
}

#[inline(always)]
fn sub(mut lhs: PortableVector, rhs: &PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs[i] -= rhs[i];
    }

    lhs
}

#[inline(always)]
fn multiply_by_constant(mut v: PortableVector, c: i32) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v[i] *= c;
    }

    v
}

#[inline(always)]
fn bitwise_and_with_constant(mut v: PortableVector, c: i32) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v[i] &= c;
    }

    v
}

#[inline(always)]
fn shift_right<const SHIFT_BY: i32>(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v[i] = v[i] >> SHIFT_BY;
    }

    v
}

#[inline(always)]
fn shift_left<const SHIFT_BY: i32>(mut lhs: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs[i] = lhs[i] << SHIFT_BY;
    }

    lhs
}

#[inline(always)]
fn cond_subtract_3329(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        debug_assert!(v[i] >= 0 && v[i] < 4096);
        if v[i] >= 3329 {
            v[i] -= 3329
        }
    }
    v
}

#[inline(always)]
fn barrett_reduce(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v[i] = crate::arithmetic::barrett_reduce(v[i]);
    }

    v
}

#[inline(always)]
fn montgomery_reduce(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v[i] = crate::arithmetic::montgomery_reduce(v[i]);
    }

    v
}

#[inline(always)]
fn compress_1(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v[i] = compress_message_coefficient(v[i] as u16) as i32;
    }

    v
}

#[inline(always)]
fn compress<const COEFFICIENT_BITS: i32>(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v[i] =
            compress_ciphertext_coefficient(COEFFICIENT_BITS as u8, v[i] as u16) as i32;
    }
    v
}

#[inline(always)]
fn ntt_layer_1_step(mut v: PortableVector, zeta1: i32, zeta2: i32) -> PortableVector {
    let t = montgomery_multiply_fe_by_fer(v[2], zeta1);
    v[2] = v[0] - t;
    v[0] = v[0] + t;

    let t = montgomery_multiply_fe_by_fer(v[3], zeta1);
    v[3] = v[1] - t;
    v[1] = v[1] + t;

    let t = montgomery_multiply_fe_by_fer(v[6], zeta2);
    v[6] = v[4] - t;
    v[4] = v[4] + t;

    let t = montgomery_multiply_fe_by_fer(v[7], zeta2);
    v[7] = v[5] - t;
    v[5] = v[5] + t;

    v
}

#[inline(always)]
fn ntt_layer_2_step(mut v: PortableVector, zeta: i32) -> PortableVector {
    let t = montgomery_multiply_fe_by_fer(v[4], zeta);
    v[4] = v[0] - t;
    v[0] = v[0] + t;

    let t = montgomery_multiply_fe_by_fer(v[5], zeta);
    v[5] = v[1] - t;
    v[1] = v[1] + t;

    let t = montgomery_multiply_fe_by_fer(v[6], zeta);
    v[6] = v[2] - t;
    v[2] = v[2] + t;

    let t = montgomery_multiply_fe_by_fer(v[7], zeta);
    v[7] = v[3] - t;
    v[3] = v[3] + t;

    v
}

#[inline(always)]
fn inv_ntt_layer_1_step(mut v: PortableVector, zeta1: i32, zeta2: i32) -> PortableVector {
    let a_minus_b = v[2] - v[0];
    v[0] = v[0] + v[2];
    v[2] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = v[3] - v[1];
    v[1] = v[1] + v[3];
    v[3] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = v[6] - v[4];
    v[4] = v[4] + v[6];
    v[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);

    let a_minus_b = v[7] - v[5];
    v[5] = v[5] + v[7];
    v[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);

    v
}

#[inline(always)]
fn inv_ntt_layer_2_step(mut v: PortableVector, zeta: i32) -> PortableVector {
    let a_minus_b = v[4] - v[0];
    v[0] = v[0] + v[4];
    v[4] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v[5] - v[1];
    v[1] = v[1] + v[5];
    v[5] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v[6] - v[2];
    v[2] = v[2] + v[6];
    v[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v[7] - v[3];
    v[3] = v[3] + v[7];
    v[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    v
}

#[inline(always)]
fn ntt_multiply(
    lhs: &PortableVector,
    rhs: &PortableVector,
    zeta0: i32,
    zeta1: i32,
) -> PortableVector {
    let mut out = PortableVector::ZERO();
    let product = ntt_multiply_binomials(
        (lhs[0], lhs[1]),
        (rhs[0], rhs[1]),
        zeta0,
    );
    out[0] = product.0;
    out[1] = product.1;

    let product = ntt_multiply_binomials(
        (lhs[2], lhs[3]),
        (rhs[2], rhs[3]),
        -zeta0,
    );
    out[2] = product.0;
    out[3] = product.1;

    let product = ntt_multiply_binomials(
        (lhs[4], lhs[5]),
        (rhs[4], rhs[5]),
        zeta1,
    );
    out[4] = product.0;
    out[5] = product.1;

    let product = ntt_multiply_binomials(
        (lhs[6], lhs[7]),
        (rhs[6], rhs[7]),
        -zeta1,
    );
    out[6] = product.0;
    out[7] = product.1;
    out
}

#[inline(always)]
fn serialize_1(v: PortableVector) -> u8 {
    let mut result = 0u8;
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        result |= (v[i] as u8) << i;
    }

    result
}

#[inline(always)]
fn deserialize_1(v: u8) -> PortableVector {
    let mut result = PortableVector::ZERO();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        result[i] = ((v >> i) & 0x1) as i32;
    }

    result
}

#[inline(always)]
fn serialize_4(v: PortableVector) -> [u8; 4] {
    let mut result = [0u8; 4];

    result[0] = ((v[1] as u8) << 4) | (v[0] as u8);
    result[1] = ((v[3] as u8) << 4) | (v[2] as u8);
    result[2] = ((v[5] as u8) << 4) | (v[4] as u8);
    result[3] = ((v[7] as u8) << 4) | (v[6] as u8);

    result
}

#[inline(always)]
fn deserialize_4(bytes: &[u8]) -> PortableVector {
    let mut v = PortableVector::ZERO();

    v[0] = (bytes[0] & 0x0F) as i32;
    v[1] = ((bytes[0] >> 4) & 0x0F) as i32;

    v[2] = (bytes[1] & 0x0F) as i32;
    v[3] = ((bytes[1] >> 4) & 0x0F) as i32;

    v[4] = (bytes[2] & 0x0F) as i32;
    v[5] = ((bytes[2] >> 4) & 0x0F) as i32;

    v[6] = (bytes[3] & 0x0F) as i32;
    v[7] = ((bytes[3] >> 4) & 0x0F) as i32;

    v
}

#[inline(always)]
fn serialize_5(v: PortableVector) -> [u8; 5] {
    let mut result = [0u8; 5];

    result[0] = ((v[1] & 0x7) << 5 | v[0]) as u8;
    result[1] = (((v[3] & 1) << 7) | (v[2] << 2) | (v[1] >> 3)) as u8;
    result[2] = (((v[4] & 0xF) << 4) | (v[3] >> 1)) as u8;
    result[3] = (((v[6] & 0x3) << 6) | (v[5] << 1) | (v[4] >> 4)) as u8;
    result[4] = ((v[7] << 3) | (v[6] >> 2)) as u8;

    result
}

#[inline(always)]
fn deserialize_5(bytes: &[u8]) -> PortableVector {
    let mut v = PortableVector::ZERO();

    v[0] = (bytes[0] & 0x1F) as i32;
    v[1] = ((bytes[1] & 0x3) << 3 | (bytes[0] >> 5)) as i32;
    v[2] = ((bytes[1] >> 2) & 0x1F) as i32;
    v[3] = (((bytes[2] & 0xF) << 1) | (bytes[1] >> 7)) as i32;
    v[4] = (((bytes[3] & 1) << 4) | (bytes[2] >> 4)) as i32;
    v[5] = ((bytes[3] >> 1) & 0x1F) as i32;
    v[6] = (((bytes[4] & 0x7) << 2) | (bytes[3] >> 6)) as i32;
    v[7] = (bytes[4] >> 3) as i32;

    v
}

#[inline(always)]
fn serialize_10(v: PortableVector) -> [u8; 10] {
    let mut result = [0u8; 10];

    result[0] = (v[0] & 0xFF) as u8;
    result[1] = ((v[1] & 0x3F) as u8) << 2 | ((v[0] >> 8) & 0x03) as u8;
    result[2] = ((v[2] & 0x0F) as u8) << 4 | ((v[1] >> 6) & 0x0F) as u8;
    result[3] = ((v[3] & 0x03) as u8) << 6 | ((v[2] >> 4) & 0x3F) as u8;
    result[4] = ((v[3] >> 2) & 0xFF) as u8;

    result[5] = (v[4] & 0xFF) as u8;
    result[6] = ((v[5] & 0x3F) as u8) << 2 | ((v[4] >> 8) & 0x03) as u8;
    result[7] = ((v[6] & 0x0F) as u8) << 4 | ((v[5] >> 6) & 0x0F) as u8;
    result[8] = ((v[7] & 0x03) as u8) << 6 | ((v[6] >> 4) & 0x3F) as u8;
    result[9] = ((v[7] >> 2) & 0xFF) as u8;

    result
}

#[inline(always)]
fn deserialize_10(bytes: &[u8]) -> PortableVector {
    let mut result = PortableVector::ZERO();

    result[0] = ((bytes[1] as i32 & 0x03) << 8 | (bytes[0] as i32 & 0xFF)) as i32;
    result[1] = ((bytes[2] as i32 & 0x0F) << 6 | (bytes[1] as i32 >> 2)) as i32;
    result[2] = ((bytes[3] as i32 & 0x3F) << 4 | (bytes[2] as i32 >> 4)) as i32;
    result[3] = (((bytes[4] as i32) << 2) | (bytes[3] as i32 >> 6)) as i32;

    result[4] = ((bytes[6] as i32 & 0x03) << 8 | (bytes[5] as i32 & 0xFF)) as i32;
    result[5] = ((bytes[7] as i32 & 0x0F) << 6 | (bytes[6] as i32 >> 2)) as i32;
    result[6] = ((bytes[8] as i32 & 0x3F) << 4 | (bytes[7] as i32 >> 4)) as i32;
    result[7] = (((bytes[9] as i32) << 2) | (bytes[8] as i32 >> 6)) as i32;

    result
}

#[inline(always)]
fn serialize_11(v: PortableVector) -> [u8; 11] {
    let mut result = [0u8; 11];
    result[0] = v[0] as u8;
    result[1] = ((v[1] & 0x1F) as u8) << 3 | ((v[0] >> 8) as u8);
    result[2] = ((v[2] & 0x3) as u8) << 6 | ((v[1] >> 5) as u8);
    result[3] = ((v[2] >> 2) & 0xFF) as u8;
    result[4] = ((v[3] & 0x7F) as u8) << 1 | (v[2] >> 10) as u8;
    result[5] = ((v[4] & 0xF) as u8) << 4 | (v[3] >> 7) as u8;
    result[6] = ((v[5] & 0x1) as u8) << 7 | (v[4] >> 4) as u8;
    result[7] = ((v[5] >> 1) & 0xFF) as u8;
    result[8] = ((v[6] & 0x3F) as u8) << 2 | (v[5] >> 9) as u8;
    result[9] = ((v[7] & 0x7) as u8) << 5 | (v[6] >> 6) as u8;
    result[10] = (v[7] >> 3) as u8;
    result
}

#[inline(always)]
fn deserialize_11(bytes: &[u8]) -> PortableVector {
    let mut result = PortableVector::ZERO();
    result[0] = ((bytes[1] as i32 & 0x7) << 8 | bytes[0] as i32) as i32;
    result[1] = ((bytes[2] as i32 & 0x3F) << 5 | (bytes[1] as i32 >> 3)) as i32;
    result[2] = ((bytes[4] as i32 & 0x1) << 10
        | ((bytes[3] as i32) << 2)
        | ((bytes[2] as i32) >> 6)) as i32;
    result[3] = ((bytes[5] as i32 & 0xF) << 7 | (bytes[4] as i32 >> 1)) as i32;
    result[4] = ((bytes[6] as i32 & 0x7F) << 4 | (bytes[5] as i32 >> 4)) as i32;
    result[5] =
        ((bytes[8] as i32 & 0x3) << 9 | ((bytes[7] as i32) << 1) | ((bytes[6] as i32) >> 7)) as i32;
    result[6] = ((bytes[9] as i32 & 0x1F) << 6 | (bytes[8] as i32 >> 2)) as i32;
    result[7] = (((bytes[10] as i32) << 3) | (bytes[9] as i32 >> 5)) as i32;
    result
}

#[inline(always)]
fn serialize_12(v: PortableVector) -> [u8; 12] {
    let mut result = [0u8; 12];

    result[0] = (v[0] & 0xFF) as u8;
    result[1] = ((v[0] >> 8) | ((v[1] & 0x0F) << 4)) as u8;
    result[2] = ((v[1] >> 4) & 0xFF) as u8;

    result[3] = (v[2] & 0xFF) as u8;
    result[4] = ((v[2] >> 8) | ((v[3] & 0x0F) << 4)) as u8;
    result[5] = ((v[3] >> 4) & 0xFF) as u8;

    result[6] = (v[4] & 0xFF) as u8;
    result[7] = ((v[4] >> 8) | ((v[5] & 0x0F) << 4)) as u8;
    result[8] = ((v[5] >> 4) & 0xFF) as u8;

    result[9] = (v[6] & 0xFF) as u8;
    result[10] = ((v[6] >> 8) | ((v[7] & 0x0F) << 4)) as u8;
    result[11] = ((v[7] >> 4) & 0xFF) as u8;

    result
}

#[inline(always)]
fn deserialize_12(bytes: &[u8]) -> PortableVector {
    let mut re = PortableVector::ZERO();

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

    re[0] = (byte1 & 0x0F) << 8 | (byte0 & 0xFF);
    re[1] = (byte2 << 4) | ((byte1 >> 4) & 0x0F);

    re[2] = (byte4 & 0x0F) << 8 | (byte3 & 0xFF);
    re[3] = (byte5 << 4) | ((byte4 >> 4) & 0x0F);

    re[4] = (byte7 & 0x0F) << 8 | (byte6 & 0xFF);
    re[5] = (byte8 << 4) | ((byte7 >> 4) & 0x0F);

    re[6] = (byte10 & 0x0F) << 8 | (byte9 & 0xFF);
    re[7] = (byte11 << 4) | ((byte10 >> 4) & 0x0F);

    re
}

impl Operations for PortableVector {
    fn ZERO() -> Self {
        ZERO()
    }

    fn to_i32_array(v: Self) -> [i32; 8] {
        to_i32_array(v)
    }

    fn from_i32_array(array: [i32; 8]) -> Self {
        from_i32_array(array)
    }

    fn add_constant(v: Self, c: i32) -> Self {
        add_constant(v, c)
    }

    fn add(lhs: Self, rhs: &Self) -> Self {
        add(lhs, rhs)
    }

    fn sub(lhs: Self, rhs: &Self) -> Self {
        sub(lhs, rhs)
    }

    fn multiply_by_constant(v: Self, c: i32) -> Self {
        multiply_by_constant(v, c)
    }

    fn bitwise_and_with_constant(v: Self, c: i32) -> Self {
        bitwise_and_with_constant(v, c)
    }

    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_right::<{ SHIFT_BY }>(v)
    }

    fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_left::<{ SHIFT_BY }>(v)
    }

    fn cond_subtract_3329(v: Self) -> Self {
        cond_subtract_3329(v)
    }

    fn barrett_reduce(v: Self) -> Self {
        barrett_reduce(v)
    }

    fn montgomery_reduce(v: Self) -> Self {
        montgomery_reduce(v)
    }

    fn compress_1(v: Self) -> Self {
        compress_1(v)
    }

    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        compress::<COEFFICIENT_BITS>(v)
    }

    fn ntt_layer_1_step(a: Self, zeta1: i32, zeta2: i32) -> Self {
        ntt_layer_1_step(a, zeta1, zeta2)
    }

    fn ntt_layer_2_step(a: Self, zeta: i32) -> Self {
        ntt_layer_2_step(a, zeta)
    }

    fn inv_ntt_layer_1_step(a: Self, zeta1: i32, zeta2: i32) -> Self {
        inv_ntt_layer_1_step(a, zeta1, zeta2)
    }

    fn inv_ntt_layer_2_step(a: Self, zeta: i32) -> Self {
        inv_ntt_layer_2_step(a, zeta)
    }

    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i32, zeta1: i32) -> Self {
        ntt_multiply(lhs, rhs, zeta0, zeta1)
    }

    fn serialize_1(a: Self) -> u8 {
        serialize_1(a)
    }

    fn deserialize_1(a: u8) -> Self {
        deserialize_1(a)
    }

    fn serialize_4(a: Self) -> [u8; 4] {
        serialize_4(a)
    }

    fn deserialize_4(a: &[u8]) -> Self {
        deserialize_4(a)
    }

    fn serialize_5(a: Self) -> [u8; 5] {
        serialize_5(a)
    }

    fn deserialize_5(a: &[u8]) -> Self {
        deserialize_5(a)
    }

    fn serialize_10(a: Self) -> [u8; 10] {
        serialize_10(a)
    }

    fn deserialize_10(a: &[u8]) -> Self {
        deserialize_10(a)
    }

    fn serialize_11(a: Self) -> [u8; 11] {
        serialize_11(a)
    }

    fn deserialize_11(a: &[u8]) -> Self {
        deserialize_11(a)
    }

    fn serialize_12(a: Self) -> [u8; 12] {
        serialize_12(a)
    }

    fn deserialize_12(a: &[u8]) -> Self {
        deserialize_12(a)
    }
}
