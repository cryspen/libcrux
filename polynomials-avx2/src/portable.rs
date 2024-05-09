use libcrux_traits::INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
pub use libcrux_traits::{FIELD_ELEMENTS_IN_VECTOR, FIELD_MODULUS};

type FieldElement = i16;
type MontgomeryFieldElement = i16;
type FieldElementTimesMontgomeryR = i16;
const MONTGOMERY_SHIFT: u8 = 16;
const MONTGOMERY_R: i32 = 1 << MONTGOMERY_SHIFT;

const BARRETT_SHIFT: i32 = 26;
const BARRETT_R: i32 = 1 << BARRETT_SHIFT;
const BARRETT_MULTIPLIER: i32 = 20159;

pub(crate) fn get_n_least_significant_bits(n: u8, value: u32) -> u32 {
    // hax_debug_assert!(n == 4 || n == 5 || n == 10 || n == 11 || n == MONTGOMERY_SHIFT);

    value & ((1 << n) - 1)
}

pub(crate) fn montgomery_reduce_element(value: i32) -> MontgomeryFieldElement {
    // This forces hax to extract code for MONTGOMERY_R before it extracts code
    // for this function. The removal of this line is being tracked in:
    // https://github.com/cryspen/libcrux/issues/134
    let _ = MONTGOMERY_R;

    let k = (value as i16) as i32 * (INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);
    let k_times_modulus = (k as i16 as i32) * (FIELD_MODULUS as i32);

    let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    let value_high = (value >> MONTGOMERY_SHIFT) as i16;

    value_high - c
}

#[inline(always)]
pub(crate) fn montgomery_multiply_fe_by_fer(
    fe: FieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> FieldElement {
    montgomery_reduce_element((fe as i32) * (fer as i32))
}

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constant(mut v: PortableVector, c: i16) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = montgomery_multiply_fe_by_fer(v.elements[i], c)
    }
    v
}

pub(crate) fn compress_ciphertext_coefficient(coefficient_bits: u8, fe: u16) -> FieldElement {
    // This has to be constant time due to:
    // https://groups.google.com/a/list.nist.gov/g/pqc-forum/c/ldX0ThYJuBo/m/ovODsdY7AwAJ
    let mut compressed = (fe as u64) << coefficient_bits;
    compressed += 1664 as u64;

    compressed *= 10_321_340;
    compressed >>= 35;

    get_n_least_significant_bits(coefficient_bits, compressed as u32) as FieldElement
}

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

pub(crate) fn barrett_reduce_element(value: FieldElement) -> FieldElement {
    // hax_debug_assert!(
    //     i32::from(value) > -BARRETT_R && i32::from(value) < BARRETT_R,
    //     "value is {value}"
    // );

    let t = (i32::from(value) * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    let quotient = (t >> BARRETT_SHIFT) as i16;

    let result = value - (quotient * FIELD_MODULUS);

    // hax_debug_assert!(
    //     result > -FIELD_MODULUS && result < FIELD_MODULUS,
    //     "value is {value}"
    // );

    result
}

#[inline(always)]
pub(crate) fn barrett_reduce(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = barrett_reduce_element(v.elements[i]);
    }

    v
}

#[inline(always)]
pub(crate) fn compress<const COEFFICIENT_BITS: i32>(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] =
            compress_ciphertext_coefficient(COEFFICIENT_BITS as u8, v.elements[i] as u16) as i16;
    }
    v
}

#[inline(always)]
pub(crate) fn decompress<const COEFFICIENT_BITS: i32>(mut v: PortableVector) -> PortableVector {
    debug_assert!(to_i16_array(v)
        .into_iter()
        .all(|coefficient| coefficient.abs() < 1 << COEFFICIENT_BITS));

    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        let mut decompressed = v.elements[i] as i32 * FIELD_MODULUS as i32;
        decompressed = (decompressed << 1) + (1i32 << COEFFICIENT_BITS);
        decompressed = decompressed >> (COEFFICIENT_BITS + 1);
        v.elements[i] = decompressed as i16;
    }

    debug_assert!(to_i16_array(v)
        .into_iter()
        .all(|coefficient| coefficient.abs() as u16 <= 1 << 12));

    v
}

#[inline(always)]
pub(crate) fn ntt_layer_1_step(
    mut v: PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    // First 8 elements.
    let t = montgomery_multiply_fe_by_fer(v.elements[2], zeta0);
    v.elements[2] = v.elements[0] - t;
    v.elements[0] = v.elements[0] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[3], zeta0);
    v.elements[3] = v.elements[1] - t;
    v.elements[1] = v.elements[1] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[6], zeta1);
    v.elements[6] = v.elements[4] - t;
    v.elements[4] = v.elements[4] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[7], zeta1);
    v.elements[7] = v.elements[5] - t;
    v.elements[5] = v.elements[5] + t;

    // Next 8 elements.
    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 2], zeta2);
    v.elements[8 + 2] = v.elements[8 + 0] - t;
    v.elements[8 + 0] = v.elements[8 + 0] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 3], zeta2);
    v.elements[8 + 3] = v.elements[8 + 1] - t;
    v.elements[8 + 1] = v.elements[8 + 1] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 6], zeta3);
    v.elements[8 + 6] = v.elements[8 + 4] - t;
    v.elements[8 + 4] = v.elements[8 + 4] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 7], zeta3);
    v.elements[8 + 7] = v.elements[8 + 5] - t;
    v.elements[8 + 5] = v.elements[8 + 5] + t;

    v
}

#[inline(always)]
pub(crate) fn ntt_layer_3_step(mut v: PortableVector, zeta: i16) -> PortableVector {
    let t = montgomery_multiply_fe_by_fer(v.elements[8], zeta);
    v.elements[8] = v.elements[0] - t;
    v.elements[0] = v.elements[0] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[9], zeta);
    v.elements[9] = v.elements[1] - t;
    v.elements[1] = v.elements[1] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[10], zeta);
    v.elements[10] = v.elements[2] - t;
    v.elements[2] = v.elements[2] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[11], zeta);
    v.elements[11] = v.elements[3] - t;
    v.elements[3] = v.elements[3] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[12], zeta);
    v.elements[12] = v.elements[4] - t;
    v.elements[4] = v.elements[4] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[13], zeta);
    v.elements[13] = v.elements[5] - t;
    v.elements[5] = v.elements[5] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[14], zeta);
    v.elements[14] = v.elements[6] - t;
    v.elements[6] = v.elements[6] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[15], zeta);
    v.elements[15] = v.elements[7] - t;
    v.elements[7] = v.elements[7] + t;

    v
}

#[inline(always)]
pub(crate) fn ntt_layer_2_step(mut v: PortableVector, zeta0: i16, zeta1: i16) -> PortableVector {
    // First 8 elements.
    let t = montgomery_multiply_fe_by_fer(v.elements[4], zeta0);
    v.elements[4] = v.elements[0] - t;
    v.elements[0] = v.elements[0] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[5], zeta0);
    v.elements[5] = v.elements[1] - t;
    v.elements[1] = v.elements[1] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[6], zeta0);
    v.elements[6] = v.elements[2] - t;
    v.elements[2] = v.elements[2] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[7], zeta0);
    v.elements[7] = v.elements[3] - t;
    v.elements[3] = v.elements[3] + t;

    // Next 8 elements.
    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 4], zeta1);
    v.elements[8 + 4] = v.elements[8 + 0] - t;
    v.elements[8 + 0] = v.elements[8 + 0] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 5], zeta1);
    v.elements[8 + 5] = v.elements[8 + 1] - t;
    v.elements[8 + 1] = v.elements[8 + 1] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 6], zeta1);
    v.elements[8 + 6] = v.elements[8 + 2] - t;
    v.elements[8 + 2] = v.elements[8 + 2] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 7], zeta1);
    v.elements[8 + 7] = v.elements[8 + 3] - t;
    v.elements[8 + 3] = v.elements[8 + 3] + t;

    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_1_step(
    mut v: PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    // First 8 elements.
    let a_minus_b = v.elements[2] - v.elements[0];
    v.elements[0] = barrett_reduce_element(v.elements[0] + v.elements[2]);
    v.elements[2] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = v.elements[3] - v.elements[1];
    v.elements[1] = barrett_reduce_element(v.elements[1] + v.elements[3]);
    v.elements[3] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = v.elements[6] - v.elements[4];
    v.elements[4] = barrett_reduce_element(v.elements[4] + v.elements[6]);
    v.elements[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = v.elements[7] - v.elements[5];
    v.elements[5] = barrett_reduce_element(v.elements[5] + v.elements[7]);
    v.elements[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    // Next 8 elements.
    let a_minus_b = v.elements[8 + 2] - v.elements[8 + 0];
    v.elements[8 + 0] = barrett_reduce_element(v.elements[8 + 0] + v.elements[8 + 2]);
    v.elements[8 + 2] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);

    let a_minus_b = v.elements[8 + 3] - v.elements[8 + 1];
    v.elements[8 + 1] = barrett_reduce_element(v.elements[8 + 1] + v.elements[8 + 3]);
    v.elements[8 + 3] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);

    let a_minus_b = v.elements[8 + 6] - v.elements[8 + 4];
    v.elements[8 + 4] = barrett_reduce_element(v.elements[8 + 4] + v.elements[8 + 6]);
    v.elements[8 + 6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta3);

    let a_minus_b = v.elements[8 + 7] - v.elements[8 + 5];
    v.elements[8 + 5] = barrett_reduce_element(v.elements[8 + 5] + v.elements[8 + 7]);
    v.elements[8 + 7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta3);

    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_step(
    mut v: PortableVector,
    zeta0: i16,
    zeta1: i16,
) -> PortableVector {
    // First 8 elements.
    let a_minus_b = v.elements[4] - v.elements[0];
    v.elements[0] = v.elements[0] + v.elements[4];
    v.elements[4] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = v.elements[5] - v.elements[1];
    v.elements[1] = v.elements[1] + v.elements[5];
    v.elements[5] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = v.elements[6] - v.elements[2];
    v.elements[2] = v.elements[2] + v.elements[6];
    v.elements[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = v.elements[7] - v.elements[3];
    v.elements[3] = v.elements[3] + v.elements[7];
    v.elements[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    // Next 8 elements.
    let a_minus_b = v.elements[8 + 4] - v.elements[8 + 0];
    v.elements[8 + 0] = v.elements[8 + 0] + v.elements[8 + 4];
    v.elements[8 + 4] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = v.elements[8 + 5] - v.elements[8 + 1];
    v.elements[8 + 1] = v.elements[8 + 1] + v.elements[8 + 5];
    v.elements[8 + 5] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = v.elements[8 + 6] - v.elements[8 + 2];
    v.elements[8 + 2] = v.elements[8 + 2] + v.elements[8 + 6];
    v.elements[8 + 6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = v.elements[8 + 7] - v.elements[8 + 3];
    v.elements[8 + 3] = v.elements[8 + 3] + v.elements[8 + 7];
    v.elements[8 + 7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_3_step(mut v: PortableVector, zeta: i16) -> PortableVector {
    let a_minus_b = v.elements[8] - v.elements[0];
    v.elements[0] = v.elements[0] + v.elements[8];
    v.elements[8] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[9] - v.elements[1];
    v.elements[1] = v.elements[1] + v.elements[9];
    v.elements[9] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[10] - v.elements[2];
    v.elements[2] = v.elements[2] + v.elements[10];
    v.elements[10] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[11] - v.elements[3];
    v.elements[3] = v.elements[3] + v.elements[11];
    v.elements[11] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[12] - v.elements[4];
    v.elements[4] = v.elements[4] + v.elements[12];
    v.elements[12] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[13] - v.elements[5];
    v.elements[5] = v.elements[5] + v.elements[13];
    v.elements[13] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[14] - v.elements[6];
    v.elements[6] = v.elements[6] + v.elements[14];
    v.elements[14] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[15] - v.elements[7];
    v.elements[7] = v.elements[7] + v.elements[15];
    v.elements[15] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    v
}

#[inline(always)]
pub(crate) fn ntt_multiply_binomials(
    (a0, a1): (FieldElement, FieldElement),
    (b0, b1): (FieldElement, FieldElement),
    zeta: FieldElementTimesMontgomeryR,
) -> (MontgomeryFieldElement, MontgomeryFieldElement) {
    (
        montgomery_reduce_element(
            (a0 as i32) * (b0 as i32)
                + (montgomery_reduce_element((a1 as i32) * (b1 as i32)) as i32) * (zeta as i32),
        ),
        montgomery_reduce_element((a0 as i32) * (b1 as i32) + (a1 as i32) * (b0 as i32)),
    )
}

#[inline(always)]
pub(crate) fn ntt_multiply(
    lhs: &PortableVector,
    rhs: &PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    let mut out = zero();

    // First 8 elements.
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

    // Next 8 elements.
    let product = ntt_multiply_binomials(
        (lhs.elements[8 + 0], lhs.elements[8 + 1]),
        (rhs.elements[8 + 0], rhs.elements[8 + 1]),
        zeta2,
    );
    out.elements[8 + 0] = product.0;
    out.elements[8 + 1] = product.1;

    let product = ntt_multiply_binomials(
        (lhs.elements[8 + 2], lhs.elements[8 + 3]),
        (rhs.elements[8 + 2], rhs.elements[8 + 3]),
        -zeta2,
    );
    out.elements[8 + 2] = product.0;
    out.elements[8 + 3] = product.1;

    let product = ntt_multiply_binomials(
        (lhs.elements[8 + 4], lhs.elements[8 + 5]),
        (rhs.elements[8 + 4], rhs.elements[8 + 5]),
        zeta3,
    );
    out.elements[8 + 4] = product.0;
    out.elements[8 + 5] = product.1;

    let product = ntt_multiply_binomials(
        (lhs.elements[8 + 6], lhs.elements[8 + 7]),
        (rhs.elements[8 + 6], rhs.elements[8 + 7]),
        -zeta3,
    );
    out.elements[8 + 6] = product.0;
    out.elements[8 + 7] = product.1;

    out
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
