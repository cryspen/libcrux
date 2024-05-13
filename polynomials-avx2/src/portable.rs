pub use libcrux_traits::{FIELD_ELEMENTS_IN_VECTOR, FIELD_MODULUS};

type FieldElement = i16;

#[derive(Clone, Copy)]
pub(crate) struct PortableVector {
    elements: [FieldElement; FIELD_ELEMENTS_IN_VECTOR],
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn zero() -> PortableVector {
    PortableVector {
        elements: [0i16; FIELD_ELEMENTS_IN_VECTOR],
    }
}

#[inline(always)]
pub(crate) fn to_i16_array(v: PortableVector) -> [i16; FIELD_ELEMENTS_IN_VECTOR] {
    v.elements
}

#[inline(always)]
pub(crate) fn from_i16_array(array: [i16; FIELD_ELEMENTS_IN_VECTOR]) -> PortableVector {
    PortableVector { elements: array }
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
pub(crate) fn rej_sample(a: &[u8]) -> (usize, [i16; 16]) {
    let mut result = [0i16; 16];
    let mut sampled = 0;
    for bytes in a.chunks(3) {
        let b1 = bytes[0] as i16;
        let b2 = bytes[1] as i16;
        let b3 = bytes[2] as i16;

        let d1 = ((b2 & 0xF) << 8) | b1;
        let d2 = (b3 << 4) | (b2 >> 4);

        if d1 < FIELD_MODULUS && sampled < 16 {
            result[sampled] = d1;
            sampled += 1
        }
        if d2 < FIELD_MODULUS && sampled < 16 {
            result[sampled] = d2;
            sampled += 1
        }
    }
    (sampled, result)
}
