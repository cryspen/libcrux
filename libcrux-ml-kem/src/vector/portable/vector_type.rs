use crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR;

/// Values having this type hold a representative 'x' of the ML-KEM field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i16;

#[derive(Clone, Copy)]
pub struct PortableVector {
    pub(crate) elements: [FieldElement; FIELD_ELEMENTS_IN_VECTOR],
}

#[inline(always)]
#[hax_lib::ensures(|result| fstar!(r#"${result}.f_elements == Seq.create 16 (mk_i16 0)"#))]
pub fn zero() -> PortableVector {
    PortableVector {
        elements: [0i16; FIELD_ELEMENTS_IN_VECTOR],
    }
}

#[inline(always)]
#[hax_lib::ensures(|result| fstar!(r#"${result} == ${x}.f_elements"#))]
pub fn to_i16_array(x: PortableVector, out: &mut [i16; 16]) {
    *out = x.elements;
}

#[inline(always)]
#[hax_lib::requires(array.len() == 16)]
#[hax_lib::ensures(|result| fstar!(r#"${result}.f_elements == $array"#))]
pub fn from_i16_array(array: &[i16], out: &mut PortableVector) {
    out.elements = array[0..16].try_into().unwrap();
}

#[inline(always)]
#[hax_lib::requires(array.len() >= 32)]
pub(super) fn from_bytes(array: &[u8], out: &mut PortableVector) {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        out.elements[i] = (array[2 * i] as i16) << 8 | array[2 * i + 1] as i16;
    }
}

#[inline(always)]
#[hax_lib::requires(bytes.len() >= 32)]
pub(super) fn to_bytes(x: PortableVector, bytes: &mut [u8]) {
    let _bytes_len = bytes.len();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        hax_lib::loop_invariant!(|_i: usize| bytes.len() == _bytes_len);
        bytes[2 * i] = (x.elements[i] >> 8) as u8;
        bytes[2 * i + 1] = x.elements[i] as u8;
    }
}
