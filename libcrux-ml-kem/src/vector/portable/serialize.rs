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
pub(crate) fn serialize_4(v: PortableVector) -> [u8; 8] {
    let mut result = [0u8; 8];

    result[0] = ((v.elements[1] as u8) << 4) | (v.elements[0] as u8);
    result[1] = ((v.elements[3] as u8) << 4) | (v.elements[2] as u8);
    result[2] = ((v.elements[5] as u8) << 4) | (v.elements[4] as u8);
    result[3] = ((v.elements[7] as u8) << 4) | (v.elements[6] as u8);

    result[4] = ((v.elements[8 + 1] as u8) << 4) | (v.elements[8 + 0] as u8);
    result[5] = ((v.elements[8 + 3] as u8) << 4) | (v.elements[8 + 2] as u8);
    result[6] = ((v.elements[8 + 5] as u8) << 4) | (v.elements[8 + 4] as u8);
    result[7] = ((v.elements[8 + 7] as u8) << 4) | (v.elements[8 + 6] as u8);

    result
}

#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[u8]) -> PortableVector {
    let mut v = zero();

    v.elements[0] = (bytes[0] & 0x0F) as i16;
    v.elements[1] = ((bytes[0] >> 4) & 0x0F) as i16;
    v.elements[2] = (bytes[1] & 0x0F) as i16;
    v.elements[3] = ((bytes[1] >> 4) & 0x0F) as i16;
    v.elements[4] = (bytes[2] & 0x0F) as i16;
    v.elements[5] = ((bytes[2] >> 4) & 0x0F) as i16;
    v.elements[6] = (bytes[3] & 0x0F) as i16;
    v.elements[7] = ((bytes[3] >> 4) & 0x0F) as i16;

    v.elements[8] = (bytes[4] & 0x0F) as i16;
    v.elements[9] = ((bytes[4] >> 4) & 0x0F) as i16;
    v.elements[10] = (bytes[5] & 0x0F) as i16;
    v.elements[11] = ((bytes[5] >> 4) & 0x0F) as i16;
    v.elements[12] = (bytes[6] & 0x0F) as i16;
    v.elements[13] = ((bytes[6] >> 4) & 0x0F) as i16;
    v.elements[14] = (bytes[7] & 0x0F) as i16;
    v.elements[15] = ((bytes[7] >> 4) & 0x0F) as i16;

    v
}

#[inline(always)]
pub(crate) fn serialize_5(v: PortableVector) -> [u8; 10] {
    let mut result = [0u8; 10];

    result[0] = ((v.elements[1] & 0x7) << 5 | v.elements[0]) as u8;
    result[1] = (((v.elements[3] & 1) << 7) | (v.elements[2] << 2) | (v.elements[1] >> 3)) as u8;
    result[2] = (((v.elements[4] & 0xF) << 4) | (v.elements[3] >> 1)) as u8;
    result[3] = (((v.elements[6] & 0x3) << 6) | (v.elements[5] << 1) | (v.elements[4] >> 4)) as u8;
    result[4] = ((v.elements[7] << 3) | (v.elements[6] >> 2)) as u8;

    result[5] = ((v.elements[8 + 1] & 0x7) << 5 | v.elements[8 + 0]) as u8;
    result[6] = (((v.elements[8 + 3] & 1) << 7)
        | (v.elements[8 + 2] << 2)
        | (v.elements[8 + 1] >> 3)) as u8;
    result[7] = (((v.elements[8 + 4] & 0xF) << 4) | (v.elements[8 + 3] >> 1)) as u8;
    result[8] = (((v.elements[8 + 6] & 0x3) << 6)
        | (v.elements[8 + 5] << 1)
        | (v.elements[8 + 4] >> 4)) as u8;
    result[9] = ((v.elements[8 + 7] << 3) | (v.elements[8 + 6] >> 2)) as u8;

    result
}

#[inline(always)]
pub(crate) fn deserialize_5(bytes: &[u8]) -> PortableVector {
    let mut v = zero();

    v.elements[0] = (bytes[0] & 0x1F) as i16;
    v.elements[1] = ((bytes[1] & 0x3) << 3 | (bytes[0] >> 5)) as i16;
    v.elements[2] = ((bytes[1] >> 2) & 0x1F) as i16;
    v.elements[3] = (((bytes[2] & 0xF) << 1) | (bytes[1] >> 7)) as i16;
    v.elements[4] = (((bytes[3] & 1) << 4) | (bytes[2] >> 4)) as i16;
    v.elements[5] = ((bytes[3] >> 1) & 0x1F) as i16;
    v.elements[6] = (((bytes[4] & 0x7) << 2) | (bytes[3] >> 6)) as i16;
    v.elements[7] = (bytes[4] >> 3) as i16;

    v.elements[8] = (bytes[5 + 0] & 0x1F) as i16;
    v.elements[9] = ((bytes[5 + 1] & 0x3) << 3 | (bytes[5 + 0] >> 5)) as i16;
    v.elements[10] = ((bytes[5 + 1] >> 2) & 0x1F) as i16;
    v.elements[11] = (((bytes[5 + 2] & 0xF) << 1) | (bytes[5 + 1] >> 7)) as i16;
    v.elements[12] = (((bytes[5 + 3] & 1) << 4) | (bytes[5 + 2] >> 4)) as i16;
    v.elements[13] = ((bytes[5 + 3] >> 1) & 0x1F) as i16;
    v.elements[14] = (((bytes[5 + 4] & 0x7) << 2) | (bytes[5 + 3] >> 6)) as i16;
    v.elements[15] = (bytes[5 + 4] >> 3) as i16;

    v
}

#[inline(always)]
pub(crate) fn serialize_10(v: PortableVector) -> [u8; 20] {
    let mut result = [0u8; 20];

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

    result[10] = (v.elements[8 + 0] & 0xFF) as u8;
    result[11] = ((v.elements[8 + 1] & 0x3F) as u8) << 2 | ((v.elements[8 + 0] >> 8) & 0x03) as u8;
    result[12] = ((v.elements[8 + 2] & 0x0F) as u8) << 4 | ((v.elements[8 + 1] >> 6) & 0x0F) as u8;
    result[13] = ((v.elements[8 + 3] & 0x03) as u8) << 6 | ((v.elements[8 + 2] >> 4) & 0x3F) as u8;
    result[14] = ((v.elements[8 + 3] >> 2) & 0xFF) as u8;
    result[15] = (v.elements[8 + 4] & 0xFF) as u8;
    result[16] = ((v.elements[8 + 5] & 0x3F) as u8) << 2 | ((v.elements[8 + 4] >> 8) & 0x03) as u8;
    result[17] = ((v.elements[8 + 6] & 0x0F) as u8) << 4 | ((v.elements[8 + 5] >> 6) & 0x0F) as u8;
    result[18] = ((v.elements[8 + 7] & 0x03) as u8) << 6 | ((v.elements[8 + 6] >> 4) & 0x3F) as u8;
    result[19] = ((v.elements[8 + 7] >> 2) & 0xFF) as u8;

    result
}

#[inline(always)]
pub(crate) fn deserialize_10(bytes: &[u8]) -> PortableVector {
    let mut result = zero();

    result.elements[0] = ((bytes[1] as i16 & 0x03) << 8 | (bytes[0] as i16 & 0xFF)) as i16;
    result.elements[1] = ((bytes[2] as i16 & 0x0F) << 6 | (bytes[1] as i16 >> 2)) as i16;
    result.elements[2] = ((bytes[3] as i16 & 0x3F) << 4 | (bytes[2] as i16 >> 4)) as i16;
    result.elements[3] = (((bytes[4] as i16) << 2) | (bytes[3] as i16 >> 6)) as i16;
    result.elements[4] = ((bytes[6] as i16 & 0x03) << 8 | (bytes[5] as i16 & 0xFF)) as i16;
    result.elements[5] = ((bytes[7] as i16 & 0x0F) << 6 | (bytes[6] as i16 >> 2)) as i16;
    result.elements[6] = ((bytes[8] as i16 & 0x3F) << 4 | (bytes[7] as i16 >> 4)) as i16;
    result.elements[7] = (((bytes[9] as i16) << 2) | (bytes[8] as i16 >> 6)) as i16;

    result.elements[8] =
        ((bytes[10 + 1] as i16 & 0x03) << 8 | (bytes[10 + 0] as i16 & 0xFF)) as i16;
    result.elements[9] = ((bytes[10 + 2] as i16 & 0x0F) << 6 | (bytes[10 + 1] as i16 >> 2)) as i16;
    result.elements[10] = ((bytes[10 + 3] as i16 & 0x3F) << 4 | (bytes[10 + 2] as i16 >> 4)) as i16;
    result.elements[11] = (((bytes[10 + 4] as i16) << 2) | (bytes[10 + 3] as i16 >> 6)) as i16;
    result.elements[12] =
        ((bytes[10 + 6] as i16 & 0x03) << 8 | (bytes[10 + 5] as i16 & 0xFF)) as i16;
    result.elements[13] = ((bytes[10 + 7] as i16 & 0x0F) << 6 | (bytes[10 + 6] as i16 >> 2)) as i16;
    result.elements[14] = ((bytes[10 + 8] as i16 & 0x3F) << 4 | (bytes[10 + 7] as i16 >> 4)) as i16;
    result.elements[15] = (((bytes[10 + 9] as i16) << 2) | (bytes[10 + 8] as i16 >> 6)) as i16;

    result
}

#[inline(always)]
pub(crate) fn serialize_11(v: PortableVector) -> [u8; 22] {
    let mut result = [0u8; 22];

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

    result[11] = v.elements[8 + 0] as u8;
    result[12] = ((v.elements[8 + 1] & 0x1F) as u8) << 3 | ((v.elements[8 + 0] >> 8) as u8);
    result[13] = ((v.elements[8 + 2] & 0x3) as u8) << 6 | ((v.elements[8 + 1] >> 5) as u8);
    result[14] = ((v.elements[8 + 2] >> 2) & 0xFF) as u8;
    result[15] = ((v.elements[8 + 3] & 0x7F) as u8) << 1 | (v.elements[8 + 2] >> 10) as u8;
    result[16] = ((v.elements[8 + 4] & 0xF) as u8) << 4 | (v.elements[8 + 3] >> 7) as u8;
    result[17] = ((v.elements[8 + 5] & 0x1) as u8) << 7 | (v.elements[8 + 4] >> 4) as u8;
    result[18] = ((v.elements[8 + 5] >> 1) & 0xFF) as u8;
    result[19] = ((v.elements[8 + 6] & 0x3F) as u8) << 2 | (v.elements[8 + 5] >> 9) as u8;
    result[20] = ((v.elements[8 + 7] & 0x7) as u8) << 5 | (v.elements[8 + 6] >> 6) as u8;
    result[21] = (v.elements[8 + 7] >> 3) as u8;

    result
}

#[inline(always)]
pub(crate) fn deserialize_11(bytes: &[u8]) -> PortableVector {
    let mut result = zero();

    result.elements[0] = ((bytes[1] as i16 & 0x7) << 8 | bytes[0] as i16) as i16;
    result.elements[1] = ((bytes[2] as i16 & 0x3F) << 5 | (bytes[1] as i16 >> 3)) as i16;
    result.elements[2] = ((bytes[4] as i16 & 0x1) << 10
        | ((bytes[3] as i16) << 2)
        | ((bytes[2] as i16) >> 6)) as i16;
    result.elements[3] = ((bytes[5] as i16 & 0xF) << 7 | (bytes[4] as i16 >> 1)) as i16;
    result.elements[4] = ((bytes[6] as i16 & 0x7F) << 4 | (bytes[5] as i16 >> 4)) as i16;
    result.elements[5] =
        ((bytes[8] as i16 & 0x3) << 9 | ((bytes[7] as i16) << 1) | ((bytes[6] as i16) >> 7)) as i16;
    result.elements[6] = ((bytes[9] as i16 & 0x1F) << 6 | (bytes[8] as i16 >> 2)) as i16;
    result.elements[7] = (((bytes[10] as i16) << 3) | (bytes[9] as i16 >> 5)) as i16;

    result.elements[8] = ((bytes[11 + 1] as i16 & 0x7) << 8 | bytes[11 + 0] as i16) as i16;
    result.elements[9] = ((bytes[11 + 2] as i16 & 0x3F) << 5 | (bytes[11 + 1] as i16 >> 3)) as i16;
    result.elements[10] = ((bytes[11 + 4] as i16 & 0x1) << 10
        | ((bytes[11 + 3] as i16) << 2)
        | ((bytes[11 + 2] as i16) >> 6)) as i16;
    result.elements[11] = ((bytes[11 + 5] as i16 & 0xF) << 7 | (bytes[11 + 4] as i16 >> 1)) as i16;
    result.elements[12] = ((bytes[11 + 6] as i16 & 0x7F) << 4 | (bytes[11 + 5] as i16 >> 4)) as i16;
    result.elements[13] = ((bytes[11 + 8] as i16 & 0x3) << 9
        | ((bytes[11 + 7] as i16) << 1)
        | ((bytes[11 + 6] as i16) >> 7)) as i16;
    result.elements[14] = ((bytes[11 + 9] as i16 & 0x1F) << 6 | (bytes[11 + 8] as i16 >> 2)) as i16;
    result.elements[15] = (((bytes[11 + 10] as i16) << 3) | (bytes[11 + 9] as i16 >> 5)) as i16;

    result
}

#[inline(always)]
pub(crate) fn serialize_12(v: PortableVector) -> [u8; 24] {
    let mut result = [0u8; 24];

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

    result[12] = (v.elements[8 + 0] & 0xFF) as u8;
    result[13] = ((v.elements[8 + 0] >> 8) | ((v.elements[8 + 1] & 0x0F) << 4)) as u8;
    result[14] = ((v.elements[8 + 1] >> 4) & 0xFF) as u8;
    result[15] = (v.elements[8 + 2] & 0xFF) as u8;
    result[16] = ((v.elements[8 + 2] >> 8) | ((v.elements[8 + 3] & 0x0F) << 4)) as u8;
    result[17] = ((v.elements[8 + 3] >> 4) & 0xFF) as u8;
    result[18] = (v.elements[8 + 4] & 0xFF) as u8;
    result[19] = ((v.elements[8 + 4] >> 8) | ((v.elements[8 + 5] & 0x0F) << 4)) as u8;
    result[20] = ((v.elements[8 + 5] >> 4) & 0xFF) as u8;
    result[21] = (v.elements[8 + 6] & 0xFF) as u8;
    result[22] = ((v.elements[8 + 6] >> 8) | ((v.elements[8 + 7] & 0x0F) << 4)) as u8;
    result[23] = ((v.elements[8 + 7] >> 4) & 0xFF) as u8;

    result
}

#[inline(always)]
pub(crate) fn deserialize_12(bytes: &[u8]) -> PortableVector {
    let mut re = zero();

    let byte0 = bytes[0] as i16;
    let byte1 = bytes[1] as i16;
    let byte2 = bytes[2] as i16;
    let byte3 = bytes[3] as i16;
    let byte4 = bytes[4] as i16;
    let byte5 = bytes[5] as i16;
    let byte6 = bytes[6] as i16;
    let byte7 = bytes[7] as i16;
    let byte8 = bytes[8] as i16;
    let byte9 = bytes[9] as i16;
    let byte10 = bytes[10] as i16;
    let byte11 = bytes[11] as i16;

    re.elements[0] = (byte1 & 0x0F) << 8 | (byte0 & 0xFF);
    re.elements[1] = (byte2 << 4) | ((byte1 >> 4) & 0x0F);
    re.elements[2] = (byte4 & 0x0F) << 8 | (byte3 & 0xFF);
    re.elements[3] = (byte5 << 4) | ((byte4 >> 4) & 0x0F);
    re.elements[4] = (byte7 & 0x0F) << 8 | (byte6 & 0xFF);
    re.elements[5] = (byte8 << 4) | ((byte7 >> 4) & 0x0F);
    re.elements[6] = (byte10 & 0x0F) << 8 | (byte9 & 0xFF);
    re.elements[7] = (byte11 << 4) | ((byte10 >> 4) & 0x0F);

    let byte12 = bytes[12] as i16;
    let byte13 = bytes[13] as i16;
    let byte14 = bytes[14] as i16;
    let byte15 = bytes[15] as i16;
    let byte16 = bytes[16] as i16;
    let byte17 = bytes[17] as i16;
    let byte18 = bytes[18] as i16;
    let byte19 = bytes[19] as i16;
    let byte20 = bytes[20] as i16;
    let byte21 = bytes[21] as i16;
    let byte22 = bytes[22] as i16;
    let byte23 = bytes[23] as i16;

    re.elements[8] = (byte13 & 0x0F) << 8 | (byte12 & 0xFF);
    re.elements[9] = (byte14 << 4) | ((byte13 >> 4) & 0x0F);
    re.elements[10] = (byte16 & 0x0F) << 8 | (byte15 & 0xFF);
    re.elements[11] = (byte17 << 4) | ((byte16 >> 4) & 0x0F);
    re.elements[12] = (byte19 & 0x0F) << 8 | (byte18 & 0xFF);
    re.elements[13] = (byte20 << 4) | ((byte19 >> 4) & 0x0F);
    re.elements[14] = (byte22 & 0x0F) << 8 | (byte21 & 0xFF);
    re.elements[15] = (byte23 << 4) | ((byte22 >> 4) & 0x0F);

    re
}
