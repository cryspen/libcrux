use crate::vector::FIELD_ELEMENTS_IN_VECTOR;

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
pub(crate) fn serialize_11_int(v: &[i16]) -> (u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8) {
    let r0 =   v[0] as u8;
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
    (r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10)
}

#[inline(always)]
pub(crate) fn serialize_11(v: PortableVector) -> [u8; 22] {
    let r0_10 = serialize_11_int(&v.elements[0..8]);
    let r11_21 = serialize_11_int(&v.elements[8..16]);
    let mut result = [0u8; 22];
    result[0] =  r0_10.0;
    result[1] =  r0_10.1;
    result[2] =  r0_10.2;
    result[3] =  r0_10.3;
    result[4] =  r0_10.4;
    result[5] =  r0_10.5;
    result[6] =  r0_10.6;
    result[7] =  r0_10.7;
    result[8] =  r0_10.8;
    result[9] =  r0_10.9;
    result[10] = r0_10.10;
    result[11] =  r11_21.0;
    result[12] =  r11_21.1;
    result[13] =  r11_21.2;
    result[14] =  r11_21.3;
    result[15] =  r11_21.4;
    result[16] =  r11_21.5;
    result[17] =  r11_21.6;
    result[18] =  r11_21.7;
    result[19] =  r11_21.8;
    result[20] =  r11_21.9;
    result[21] =  r11_21.10;
    result
}

#[inline(always)]
pub(crate) fn deserialize_11_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let r0 = ((bytes[1] as i16 & 0x7) << 8 | bytes[0] as i16) as i16;
    let r1 = ((bytes[2] as i16 & 0x3F) << 5 | (bytes[1] as i16 >> 3)) as i16;
    let r2 = ((bytes[4] as i16 & 0x1) << 10
        | ((bytes[3] as i16) << 2)
        | ((bytes[2] as i16) >> 6)) as i16;
    let r3 = ((bytes[5] as i16 & 0xF) << 7 | (bytes[4] as i16 >> 1)) as i16;
    let r4 = ((bytes[6] as i16 & 0x7F) << 4 | (bytes[5] as i16 >> 4)) as i16;
    let r5 =
        ((bytes[8] as i16 & 0x3) << 9 | ((bytes[7] as i16) << 1) | ((bytes[6] as i16) >> 7)) as i16;
    let r6 = ((bytes[9] as i16 & 0x1F) << 6 | (bytes[8] as i16 >> 2)) as i16;
    let r7 = (((bytes[10] as i16) << 3) | (bytes[9] as i16 >> 5)) as i16;
    (r0,r1,r2,r3,r4,r5,r6,r7)
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