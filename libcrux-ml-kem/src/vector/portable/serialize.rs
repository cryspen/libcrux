//! A module for serializing and deserializing PortableVector
//! Verification status: Lax

// A general style adopted here is to first define an internal function
// called serialize_N_int or deserialize_N_int that (de)serializes
// the minimal number of inputs K such that N*K is a multiple of 8.
// These functions are then called multiple times in the main function,
// called serialize_N or deserialize_N.
// This refactoring reduces redundancy, and also makes the code easier for
// F* to handle. As a general rule, any function that modifies an array
// more than 8 times with complex expressions starts to strain F*, so
// we separate out the code that does the computation (in _int functions)
// and code that updates arrays (in the outer functions).

use super::vector_type::*;
use crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR;

#[inline(always)]
pub(crate) fn serialize_1(v: PortableVector) -> [u8; 2] {
    let mut result = [0u8; 2];
    for i in 0..8 {
        result[0] |= (v.elements[i] as u8) << i;
    }
    for i in 8..16 {
        result[1] |= (v.elements[i] as u8) << (i - 8);
    }
    result
}

#[inline(always)]
pub(crate) fn deserialize_1(v: &[u8]) -> PortableVector {
    let mut result = zero();
    for i in 0..8 {
        result.elements[i] = ((v[0] >> i) & 0x1) as i16;
    }
    for i in 8..FIELD_ELEMENTS_IN_VECTOR {
        result.elements[i] = ((v[1] >> (i - 8)) & 0x1) as i16;
    }
    result
}

#[inline(always)]
pub(crate) fn serialize_4_int(v: &[i16]) -> (u8, u8, u8, u8) {
    let result0 = ((v[1] as u8) << 4) | (v[0] as u8);
    let result1 = ((v[3] as u8) << 4) | (v[2] as u8);
    let result2 = ((v[5] as u8) << 4) | (v[4] as u8);
    let result3 = ((v[7] as u8) << 4) | (v[6] as u8);
    (result0, result1, result2, result3)
}

#[inline(always)]
pub(crate) fn serialize_4(v: PortableVector) -> [u8; 8] {
    let result0_3 = serialize_4_int(&v.elements[0..8]);
    let result4_7 = serialize_4_int(&v.elements[8..16]);
    let mut result = [0u8; 8];
    result[0] = result0_3.0;
    result[1] = result0_3.1;
    result[2] = result0_3.2;
    result[3] = result0_3.3;
    result[4] = result4_7.0;
    result[5] = result4_7.1;
    result[6] = result4_7.2;
    result[7] = result4_7.3;
    result
}

#[inline(always)]
pub(crate) fn deserialize_4_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let v0 = (bytes[0] & 0x0F) as i16;
    let v1 = ((bytes[0] >> 4) & 0x0F) as i16;
    let v2 = (bytes[1] & 0x0F) as i16;
    let v3 = ((bytes[1] >> 4) & 0x0F) as i16;
    let v4 = (bytes[2] & 0x0F) as i16;
    let v5 = ((bytes[2] >> 4) & 0x0F) as i16;
    let v6 = (bytes[3] & 0x0F) as i16;
    let v7 = ((bytes[3] >> 4) & 0x0F) as i16;
    (v0, v1, v2, v3, v4, v5, v6, v7)
}

#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[u8]) -> PortableVector {
    let v0_7 = deserialize_4_int(&bytes[0..4]);
    let v8_15 = deserialize_4_int(&bytes[4..8]);
    let mut v = zero();
    v.elements[0] = v0_7.0;
    v.elements[1] = v0_7.1;
    v.elements[2] = v0_7.2;
    v.elements[3] = v0_7.3;
    v.elements[4] = v0_7.4;
    v.elements[5] = v0_7.5;
    v.elements[6] = v0_7.6;
    v.elements[7] = v0_7.7;
    v.elements[8] = v8_15.0;
    v.elements[9] = v8_15.1;
    v.elements[10] = v8_15.2;
    v.elements[11] = v8_15.3;
    v.elements[12] = v8_15.4;
    v.elements[13] = v8_15.5;
    v.elements[14] = v8_15.6;
    v.elements[15] = v8_15.7;
    v
}

#[inline(always)]
pub(crate) fn serialize_5_int(v: &[i16]) -> (u8, u8, u8, u8, u8) {
    let r0 = (v[0] | v[1] << 5) as u8;
    let r1 = (v[1] >> 3 | v[2] << 2 | v[3] << 7) as u8;
    let r2 = (v[3] >> 1 | v[4] << 4) as u8;
    let r3 = (v[4] >> 4 | v[5] << 1 | v[6] << 6) as u8;
    let r4 = (v[6] >> 2 | v[7] << 3) as u8;
    (r0, r1, r2, r3, r4)
}

#[inline(always)]
pub(crate) fn serialize_5(v: PortableVector) -> [u8; 10] {
    let r0_4 = serialize_5_int(&v.elements[0..8]);
    let r5_9 = serialize_5_int(&v.elements[8..16]);
    let mut result = [0u8; 10];
    result[0] = r0_4.0;
    result[1] = r0_4.1;
    result[2] = r0_4.2;
    result[3] = r0_4.3;
    result[4] = r0_4.4;
    result[5] = r5_9.0;
    result[6] = r5_9.1;
    result[7] = r5_9.2;
    result[8] = r5_9.3;
    result[9] = r5_9.4;
    result
}

#[inline(always)]
pub(crate) fn deserialize_5_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let v0 = (bytes[0] & 0x1F) as i16;
    let v1 = ((bytes[1] & 0x3) << 3 | (bytes[0] >> 5)) as i16;
    let v2 = ((bytes[1] >> 2) & 0x1F) as i16;
    let v3 = (((bytes[2] & 0xF) << 1) | (bytes[1] >> 7)) as i16;
    let v4 = (((bytes[3] & 1) << 4) | (bytes[2] >> 4)) as i16;
    let v5 = ((bytes[3] >> 1) & 0x1F) as i16;
    let v6 = (((bytes[4] & 0x7) << 2) | (bytes[3] >> 6)) as i16;
    let v7 = (bytes[4] >> 3) as i16;
    (v0, v1, v2, v3, v4, v5, v6, v7)
}

#[inline(always)]
pub(crate) fn deserialize_5(bytes: &[u8]) -> PortableVector {
    let v0_7 = deserialize_5_int(&bytes[0..5]);
    let v8_15 = deserialize_5_int(&bytes[5..10]);
    let mut v = zero();
    v.elements[0] = v0_7.0;
    v.elements[1] = v0_7.1;
    v.elements[2] = v0_7.2;
    v.elements[3] = v0_7.3;
    v.elements[4] = v0_7.4;
    v.elements[5] = v0_7.5;
    v.elements[6] = v0_7.6;
    v.elements[7] = v0_7.7;
    v.elements[8] = v8_15.0;
    v.elements[9] = v8_15.1;
    v.elements[10] = v8_15.2;
    v.elements[11] = v8_15.3;
    v.elements[12] = v8_15.4;
    v.elements[13] = v8_15.5;
    v.elements[14] = v8_15.6;
    v.elements[15] = v8_15.7;
    v
}

#[inline(always)]
pub(crate) fn serialize_10_int(v: &[i16]) -> (u8, u8, u8, u8, u8) {
    let r0 = (v[0] & 0xFF) as u8;
    let r1 = ((v[1] & 0x3F) as u8) << 2 | ((v[0] >> 8) & 0x03) as u8;
    let r2 = ((v[2] & 0x0F) as u8) << 4 | ((v[1] >> 6) & 0x0F) as u8;
    let r3 = ((v[3] & 0x03) as u8) << 6 | ((v[2] >> 4) & 0x3F) as u8;
    let r4 = ((v[3] >> 2) & 0xFF) as u8;
    (r0, r1, r2, r3, r4)
}

#[inline(always)]
pub(crate) fn serialize_10(v: PortableVector) -> [u8; 20] {
    let r0_4 = serialize_10_int(&v.elements[0..4]);
    let r5_9 = serialize_10_int(&v.elements[4..8]);
    let r10_14 = serialize_10_int(&v.elements[8..12]);
    let r15_19 = serialize_10_int(&v.elements[12..16]);
    // Here we could also do, the following, but it slows F* down:
    // [r0_4.0, r0_4.1, r0_4.2, r0_4.3, r0_4.4,
    //  r5_9.0, r5_9.1, r5_9.2, r5_9.3, r5_9.4,
    //  r10_14.0, r10_14.1, r10_14.2, r10_14.3, r10_14.4,
    //  r15_19.0, r15_19.1, r15_19.2, r15_19.3, r15_19.4 ]
    // If we can fix the F* for this, the code would be more compact.
    let mut result = [0u8; 20];
    result[0] = r0_4.0;
    result[1] = r0_4.1;
    result[2] = r0_4.2;
    result[3] = r0_4.3;
    result[4] = r0_4.4;
    result[5] = r5_9.0;
    result[6] = r5_9.1;
    result[7] = r5_9.2;
    result[8] = r5_9.3;
    result[9] = r5_9.4;
    result[10] = r10_14.0;
    result[11] = r10_14.1;
    result[12] = r10_14.2;
    result[13] = r10_14.3;
    result[14] = r10_14.4;
    result[15] = r15_19.0;
    result[16] = r15_19.1;
    result[17] = r15_19.2;
    result[18] = r15_19.3;
    result[19] = r15_19.4;
    result
}

#[inline(always)]
pub(crate) fn deserialize_10_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let r0 = ((bytes[1] as i16 & 0x03) << 8 | (bytes[0] as i16 & 0xFF)) as i16;
    let r1 = ((bytes[2] as i16 & 0x0F) << 6 | (bytes[1] as i16 >> 2)) as i16;
    let r2 = ((bytes[3] as i16 & 0x3F) << 4 | (bytes[2] as i16 >> 4)) as i16;
    let r3 = (((bytes[4] as i16) << 2) | (bytes[3] as i16 >> 6)) as i16;
    let r4 = ((bytes[6] as i16 & 0x03) << 8 | (bytes[5] as i16 & 0xFF)) as i16;
    let r5 = ((bytes[7] as i16 & 0x0F) << 6 | (bytes[6] as i16 >> 2)) as i16;
    let r6 = ((bytes[8] as i16 & 0x3F) << 4 | (bytes[7] as i16 >> 4)) as i16;
    let r7 = (((bytes[9] as i16) << 2) | (bytes[8] as i16 >> 6)) as i16;
    (r0, r1, r2, r3, r4, r5, r6, r7)
}

#[inline(always)]
pub(crate) fn deserialize_10(bytes: &[u8]) -> PortableVector {
    let v0_7 = deserialize_10_int(&bytes[0..10]);
    let v8_15 = deserialize_10_int(&bytes[10..20]);
    let mut v = zero();
    v.elements[0] = v0_7.0;
    v.elements[1] = v0_7.1;
    v.elements[2] = v0_7.2;
    v.elements[3] = v0_7.3;
    v.elements[4] = v0_7.4;
    v.elements[5] = v0_7.5;
    v.elements[6] = v0_7.6;
    v.elements[7] = v0_7.7;
    v.elements[8] = v8_15.0;
    v.elements[9] = v8_15.1;
    v.elements[10] = v8_15.2;
    v.elements[11] = v8_15.3;
    v.elements[12] = v8_15.4;
    v.elements[13] = v8_15.5;
    v.elements[14] = v8_15.6;
    v.elements[15] = v8_15.7;
    v
}

#[inline(always)]
pub(crate) fn serialize_11_int(v: &[i16]) -> (u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8) {
    let r0 = v[0] as u8;
    let r1 = ((v[1] & 0x1F) as u8) << 3 | ((v[0] >> 8) as u8);
    let r2 = ((v[2] & 0x3) as u8) << 6 | ((v[1] >> 5) as u8);
    let r3 = ((v[2] >> 2) & 0xFF) as u8;
    let r4 = ((v[3] & 0x7F) as u8) << 1 | (v[2] >> 10) as u8;
    let r5 = ((v[4] & 0xF) as u8) << 4 | (v[3] >> 7) as u8;
    let r6 = ((v[5] & 0x1) as u8) << 7 | (v[4] >> 4) as u8;
    let r7 = ((v[5] >> 1) & 0xFF) as u8;
    let r8 = ((v[6] & 0x3F) as u8) << 2 | (v[5] >> 9) as u8;
    let r9 = ((v[7] & 0x7) as u8) << 5 | (v[6] >> 6) as u8;
    let r10 = (v[7] >> 3) as u8;
    (r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10)
}

#[inline(always)]
pub(crate) fn serialize_11(v: PortableVector) -> [u8; 22] {
    let r0_10 = serialize_11_int(&v.elements[0..8]);
    let r11_21 = serialize_11_int(&v.elements[8..16]);
    let mut result = [0u8; 22];
    result[0] = r0_10.0;
    result[1] = r0_10.1;
    result[2] = r0_10.2;
    result[3] = r0_10.3;
    result[4] = r0_10.4;
    result[5] = r0_10.5;
    result[6] = r0_10.6;
    result[7] = r0_10.7;
    result[8] = r0_10.8;
    result[9] = r0_10.9;
    result[10] = r0_10.10;
    result[11] = r11_21.0;
    result[12] = r11_21.1;
    result[13] = r11_21.2;
    result[14] = r11_21.3;
    result[15] = r11_21.4;
    result[16] = r11_21.5;
    result[17] = r11_21.6;
    result[18] = r11_21.7;
    result[19] = r11_21.8;
    result[20] = r11_21.9;
    result[21] = r11_21.10;
    result
}

#[inline(always)]
pub(crate) fn deserialize_11_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let r0 = ((bytes[1] as i16 & 0x7) << 8 | bytes[0] as i16) as i16;
    let r1 = ((bytes[2] as i16 & 0x3F) << 5 | (bytes[1] as i16 >> 3)) as i16;
    let r2 = ((bytes[4] as i16 & 0x1) << 10 | ((bytes[3] as i16) << 2) | ((bytes[2] as i16) >> 6))
        as i16;
    let r3 = ((bytes[5] as i16 & 0xF) << 7 | (bytes[4] as i16 >> 1)) as i16;
    let r4 = ((bytes[6] as i16 & 0x7F) << 4 | (bytes[5] as i16 >> 4)) as i16;
    let r5 =
        ((bytes[8] as i16 & 0x3) << 9 | ((bytes[7] as i16) << 1) | ((bytes[6] as i16) >> 7)) as i16;
    let r6 = ((bytes[9] as i16 & 0x1F) << 6 | (bytes[8] as i16 >> 2)) as i16;
    let r7 = (((bytes[10] as i16) << 3) | (bytes[9] as i16 >> 5)) as i16;
    (r0, r1, r2, r3, r4, r5, r6, r7)
}

#[inline(always)]
pub(crate) fn deserialize_11(bytes: &[u8]) -> PortableVector {
    let v0_7 = deserialize_11_int(&bytes[0..11]);
    let v8_15 = deserialize_11_int(&bytes[11..22]);
    let mut v = zero();
    v.elements[0] = v0_7.0;
    v.elements[1] = v0_7.1;
    v.elements[2] = v0_7.2;
    v.elements[3] = v0_7.3;
    v.elements[4] = v0_7.4;
    v.elements[5] = v0_7.5;
    v.elements[6] = v0_7.6;
    v.elements[7] = v0_7.7;
    v.elements[8] = v8_15.0;
    v.elements[9] = v8_15.1;
    v.elements[10] = v8_15.2;
    v.elements[11] = v8_15.3;
    v.elements[12] = v8_15.4;
    v.elements[13] = v8_15.5;
    v.elements[14] = v8_15.6;
    v.elements[15] = v8_15.7;
    v
}

#[inline(always)]
pub(crate) fn serialize_12_int(v: &[i16]) -> (u8, u8, u8) {
    let r0 = (v[0] & 0xFF) as u8;
    let r1 = ((v[0] >> 8) | ((v[1] & 0x0F) << 4)) as u8;
    let r2 = ((v[1] >> 4) & 0xFF) as u8;
    (r0, r1, r2)
}

#[inline(always)]
pub(crate) fn serialize_12(v: PortableVector) -> [u8; 24] {
    let r0_2 = serialize_12_int(&v.elements[0..2]);
    let r3_5 = serialize_12_int(&v.elements[2..4]);
    let r6_8 = serialize_12_int(&v.elements[4..6]);
    let r9_11 = serialize_12_int(&v.elements[6..8]);
    let r12_14 = serialize_12_int(&v.elements[8..10]);
    let r15_17 = serialize_12_int(&v.elements[10..12]);
    let r18_20 = serialize_12_int(&v.elements[12..14]);
    let r21_23 = serialize_12_int(&v.elements[14..16]);
    let mut result = [0u8; 24];
    result[0] = r0_2.0;
    result[1] = r0_2.1;
    result[2] = r0_2.2;
    result[3] = r3_5.0;
    result[4] = r3_5.1;
    result[5] = r3_5.2;
    result[6] = r6_8.0;
    result[7] = r6_8.1;
    result[8] = r6_8.2;
    result[9] = r9_11.0;
    result[10] = r9_11.1;
    result[11] = r9_11.2;
    result[12] = r12_14.0;
    result[13] = r12_14.1;
    result[14] = r12_14.2;
    result[15] = r15_17.0;
    result[16] = r15_17.1;
    result[17] = r15_17.2;
    result[18] = r18_20.0;
    result[19] = r18_20.1;
    result[20] = r18_20.2;
    result[21] = r21_23.0;
    result[22] = r21_23.1;
    result[23] = r21_23.2;
    result
}

#[inline(always)]
pub(crate) fn deserialize_12_int(bytes: &[u8]) -> (i16, i16) {
    let byte0 = bytes[0] as i16;
    let byte1 = bytes[1] as i16;
    let byte2 = bytes[2] as i16;
    let r0 = (byte1 & 0x0F) << 8 | (byte0 & 0xFF);
    let r1 = (byte2 << 4) | ((byte1 >> 4) & 0x0F);
    (r0, r1)
}

#[inline(always)]
pub(crate) fn deserialize_12(bytes: &[u8]) -> PortableVector {
    let v0_1 = deserialize_12_int(&bytes[0..3]);
    let v2_3 = deserialize_12_int(&bytes[3..6]);
    let v4_5 = deserialize_12_int(&bytes[6..9]);
    let v6_7 = deserialize_12_int(&bytes[9..12]);
    let v8_9 = deserialize_12_int(&bytes[12..15]);
    let v10_11 = deserialize_12_int(&bytes[15..18]);
    let v12_13 = deserialize_12_int(&bytes[18..21]);
    let v14_15 = deserialize_12_int(&bytes[21..24]);
    let mut re = zero();
    re.elements[0] = v0_1.0;
    re.elements[1] = v0_1.1;
    re.elements[2] = v2_3.0;
    re.elements[3] = v2_3.1;
    re.elements[4] = v4_5.0;
    re.elements[5] = v4_5.1;
    re.elements[6] = v6_7.0;
    re.elements[7] = v6_7.1;
    re.elements[8] = v8_9.0;
    re.elements[9] = v8_9.1;
    re.elements[10] = v10_11.0;
    re.elements[11] = v10_11.1;
    re.elements[12] = v12_13.0;
    re.elements[13] = v12_13.1;
    re.elements[14] = v14_15.0;
    re.elements[15] = v14_15.1;
    re
}
