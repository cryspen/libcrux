//! # Polynomials for libcrux
//!
//! This crate abstracts efficient implementations of polynomials for algorithms
//! such as ML-KEM and ML-DSA.
//!
//! The crate only defines a common API.
//! The actual implementations are in separate crates for different platforms for
//! performance reasons.
//!
//! FIXME: This is kyber specific for now.

use libcrux_traits::INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
pub use libcrux_traits::{GenericOperations, Operations, FIELD_ELEMENTS_IN_VECTOR, FIELD_MODULUS};

// There's no runtime detection here. This either exposes the real SIMD vector,
// or the portable when the feature is not set.
//
// The consumer needs to use runtime feature detection and the appropriate vector
// in each case.
#[cfg(feature = "simd128")]
pub use libcrux_polynomials_aarch64::SIMD128Vector;
#[cfg(feature = "simd256")]
pub use libcrux_polynomials_avx2::SIMD256Vector;
#[cfg(not(feature = "simd256"))]
pub type SIMD256Vector = PortableVector;
#[cfg(not(feature = "simd128"))]
pub type SIMD128Vector = PortableVector;

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
type FieldElement = i32;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R^(-1) (mod FIELD_MODULUS).
/// We use 'mfe' as a shorthand for this type
pub type MontgomeryFieldElement = i32;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub type FieldElementTimesMontgomeryR = i32;

pub(crate) const MONTGOMERY_SHIFT: u8 = 16;
pub(crate) const MONTGOMERY_R: i32 = 1 << MONTGOMERY_SHIFT;

pub(crate) const BARRETT_SHIFT: i64 = 26;
pub(crate) const BARRETT_R: i64 = 1 << BARRETT_SHIFT;
/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
pub(crate) const BARRETT_MULTIPLIER: i64 = 20159;

#[cfg_attr(hax, hax_lib::requires(n == 4 || n == 5 || n == 10 || n == 11 || n == MONTGOMERY_SHIFT))]
#[cfg_attr(hax, hax_lib::ensures(|result| result < 2u32.pow(n.into())))]
#[inline(always)]
pub(crate) fn get_n_least_significant_bits(n: u8, value: u32) -> u32 {
    // hax_debug_assert!(n == 4 || n == 5 || n == 10 || n == 11 || n == MONTGOMERY_SHIFT);

    value & ((1 << n) - 1)
}

/// Signed Montgomery Reduction
///
/// Given an input `value`, `montgomery_reduce` outputs a representative `o`
/// such that:
///
/// - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
/// - the absolute value of `o` is bound as follows:
///
/// `|result| ≤ (|value| / MONTGOMERY_R) + (FIELD_MODULUS / 2)
///
/// In particular, if `|value| ≤ FIELD_MODULUS * MONTGOMERY_R`, then `|o| < (3 · FIELD_MODULUS) / 2`.
#[cfg_attr(hax, hax_lib::requires(value >= -FIELD_MODULUS * MONTGOMERY_R && value <= FIELD_MODULUS * MONTGOMERY_R))]
#[cfg_attr(hax, hax_lib::ensures(|result| result >= -(3 * FIELD_MODULUS) / 2 && result <= (3 * FIELD_MODULUS) / 2))]
pub(crate) fn montgomery_reduce_element(value: FieldElement) -> MontgomeryFieldElement {
    // This forces hax to extract code for MONTGOMERY_R before it extracts code
    // for this function. The removal of this line is being tracked in:
    // https://github.com/cryspen/libcrux/issues/134
    let _ = MONTGOMERY_R;

    // hax_debug_assert!(
    //     value >= -FIELD_MODULUS * MONTGOMERY_R && value <= FIELD_MODULUS * MONTGOMERY_R,
    //     "value is {value}"
    // );

    let t = get_n_least_significant_bits(MONTGOMERY_SHIFT, value as u32)
        * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    let k = get_n_least_significant_bits(MONTGOMERY_SHIFT, t) as i16;

    let k_times_modulus = (k as i32) * FIELD_MODULUS;

    let c = k_times_modulus >> MONTGOMERY_SHIFT;
    let value_high = value >> MONTGOMERY_SHIFT;

    value_high - c
}

/// If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
/// `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
/// `x · y`, as follows:
///
///    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`
///
/// `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
/// `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
#[inline(always)]
pub(crate) fn montgomery_multiply_fe_by_fer(
    fe: FieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> FieldElement {
    montgomery_reduce_element(fe * fer)
}

/// The `compress_*` functions implement the `Compress` function specified in the NIST FIPS
/// 203 standard (Page 18, Expression 4.5), which is defined as:
///
/// ```plaintext
/// Compress_d: ℤq -> ℤ_{2ᵈ}
/// Compress_d(x) = ⌈(2ᵈ/q)·x⌋
/// ```
///
/// Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
///
/// ```plaintext
/// Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
///               = ⌊(2^{d+1}·x + q) / 2q⌋
/// ```
///
/// For further information about the function implementations, consult the
/// `implementation_notes.pdf` document in this directory.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[cfg_attr(hax, hax_lib::requires(fe < (crate::constants::FIELD_MODULUS as u16)))]
#[cfg_attr(hax, hax_lib::ensures(|result|
        hax_lib::implies(833 <= fe && fe <= 2596, || result == 1) &&
        hax_lib::implies(!(833 <= fe && fe <= 2596), || result == 0)
))]
pub(crate) fn compress_message_coefficient(fe: u16) -> u8 {
    // The approach used here is inspired by:
    // https://github.com/cloudflare/circl/blob/main/pke/kyber/internal/common/poly.go#L150

    // If 833 <= fe <= 2496,
    // then -832 <= shifted <= 831
    let shifted: i16 = 1664 - (fe as i16);

    // If shifted < 0, then
    // (shifted >> 15) ^ shifted = flip_bits(shifted) = -shifted - 1, and so
    // if -832 <= shifted < 0 then 0 < shifted_positive <= 831
    //
    // If shifted >= 0 then
    // (shifted >> 15) ^ shifted = shifted, and so
    // if 0 <= shifted <= 831 then 0 <= shifted_positive <= 831
    let mask = shifted >> 15;
    let shifted_to_positive = mask ^ shifted;

    let shifted_positive_in_range = shifted_to_positive - 832;

    // If x <= 831, then x - 832 <= -1, and so x - 832 < 0, which means
    // the most significant bit of shifted_positive_in_range will be 1.
    ((shifted_positive_in_range >> 15) & 1) as u8
}

#[cfg_attr(hax,
    hax_lib::requires(
        (coefficient_bits == 4 ||
         coefficient_bits == 5 ||
         coefficient_bits == 10 ||
         coefficient_bits == 11) &&
         fe < (crate::constants::FIELD_MODULUS as u16)))]
#[cfg_attr(hax,
     hax_lib::ensures(
     |result| result >= 0 && result < 2i32.pow(coefficient_bits as u32)))]
pub(crate) fn compress_ciphertext_coefficient(coefficient_bits: u8, fe: u16) -> FieldElement {
    // hax_debug_assert!(
    //     coefficient_bits == 4
    //         || coefficient_bits == 5
    //         || coefficient_bits == 10
    //         || coefficient_bits == 11
    // );
    // hax_debug_assert!(fe <= (FIELD_MODULUS as u16));

    // This has to be constant time due to:
    // https://groups.google.com/a/list.nist.gov/g/pqc-forum/c/ldX0ThYJuBo/m/ovODsdY7AwAJ
    let mut compressed = (fe as u64) << coefficient_bits;
    compressed += 1664 as u64;

    compressed *= 10_321_340;
    compressed >>= 35;

    get_n_least_significant_bits(coefficient_bits, compressed as u32) as FieldElement
}

#[derive(Clone, Copy)]
pub struct PortableVector {
    elements: [FieldElement; 8],
}

#[allow(non_snake_case)]
#[inline(always)]
fn zero() -> PortableVector {
    PortableVector {
        elements: [0i32; FIELD_ELEMENTS_IN_VECTOR],
    }
}

#[inline(always)]
fn to_i32_array(v: PortableVector) -> [i32; 8] {
    v.elements
}

#[inline(always)]
fn from_i32_array(array: [i32; 8]) -> PortableVector {
    PortableVector { elements: array }
}

#[inline(always)]
fn add_constant(mut v: PortableVector, c: i32) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] += c;
    }

    v
}

#[inline(always)]
fn add(mut lhs: PortableVector, rhs: &PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs.elements[i] += rhs.elements[i];
    }

    lhs
}

#[inline(always)]
fn sub(mut lhs: PortableVector, rhs: &PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs.elements[i] -= rhs.elements[i];
    }

    lhs
}

#[inline(always)]
fn multiply_by_constant(mut v: PortableVector, c: i32) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] *= c;
    }

    v
}

#[inline(always)]
fn bitwise_and_with_constant(mut v: PortableVector, c: i32) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] &= c;
    }

    v
}

#[inline(always)]
fn shift_right<const SHIFT_BY: i32>(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = v.elements[i] >> SHIFT_BY;
    }

    v
}

#[inline(always)]
fn shift_left<const SHIFT_BY: i32>(mut lhs: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs.elements[i] = lhs.elements[i] << SHIFT_BY;
    }

    lhs
}

#[inline(always)]
fn cond_subtract_3329(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        debug_assert!(v.elements[i] >= 0 && v.elements[i] < 4096);
        if v.elements[i] >= 3329 {
            v.elements[i] -= 3329
        }
    }
    v
}

/// Signed Barrett Reduction
///
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
///
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
///
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
///
/// In particular, if `|value| < BARRETT_R`, then `|result| < FIELD_MODULUS`.
#[cfg_attr(hax, hax_lib::requires((i64::from(value) > -BARRETT_R && i64::from(value) < BARRETT_R)))]
#[cfg_attr(hax, hax_lib::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS))]
pub(crate) fn barrett_reduce_element(value: FieldElement) -> FieldElement {
    // hax_debug_assert!(
    //     i64::from(value) > -BARRETT_R && i64::from(value) < BARRETT_R,
    //     "value is {value}"
    // );

    let t = (i64::from(value) * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    let quotient = (t >> BARRETT_SHIFT) as i32;

    let result = value - (quotient * FIELD_MODULUS);

    // hax_debug_assert!(
    //     result > -FIELD_MODULUS && result < FIELD_MODULUS,
    //     "value is {value}"
    // );

    result
}

#[inline(always)]
fn barrett_reduce(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = barrett_reduce_element(v.elements[i]);
    }

    v
}

#[inline(always)]
fn montgomery_reduce(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = montgomery_reduce_element(v.elements[i]);
    }

    v
}

#[inline(always)]
fn compress_1(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = compress_message_coefficient(v.elements[i] as u16) as i32;
    }

    v
}

#[inline(always)]
fn compress<const COEFFICIENT_BITS: i32>(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] =
            compress_ciphertext_coefficient(COEFFICIENT_BITS as u8, v.elements[i] as u16) as i32;
    }
    v
}

#[inline(always)]
fn ntt_layer_1_step(mut v: PortableVector, zeta1: i32, zeta2: i32) -> PortableVector {
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

#[inline(always)]
fn ntt_layer_2_step(mut v: PortableVector, zeta: i32) -> PortableVector {
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

#[inline(always)]
fn inv_ntt_layer_1_step(mut v: PortableVector, zeta1: i32, zeta2: i32) -> PortableVector {
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

#[inline(always)]
fn inv_ntt_layer_2_step(mut v: PortableVector, zeta: i32) -> PortableVector {
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

/// Compute the product of two Kyber binomials with respect to the
/// modulus `X² - zeta`.
///
/// This function almost implements <strong>Algorithm 11</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
///
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
///
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
/// We say "almost" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[inline(always)]
pub(crate) fn ntt_multiply_binomials(
    (a0, a1): (FieldElement, FieldElement),
    (b0, b1): (FieldElement, FieldElement),
    zeta: FieldElementTimesMontgomeryR,
) -> (MontgomeryFieldElement, MontgomeryFieldElement) {
    (
        montgomery_reduce_element(a0 * b0 + montgomery_reduce_element(a1 * b1) * zeta),
        montgomery_reduce_element(a0 * b1 + a1 * b0),
    )
}

#[inline(always)]
fn ntt_multiply(
    lhs: &PortableVector,
    rhs: &PortableVector,
    zeta0: i32,
    zeta1: i32,
) -> PortableVector {
    let mut out = ZERO();
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

#[inline(always)]
fn serialize_1(v: PortableVector) -> u8 {
    let mut result = 0u8;
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        result |= (v.elements[i] as u8) << i;
    }

    result
}

#[inline(always)]
fn deserialize_1(v: u8) -> PortableVector {
    let mut result = ZERO();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        result.elements[i] = ((v >> i) & 0x1) as i32;
    }

    result
}

#[inline(always)]
fn serialize_4(v: PortableVector) -> [u8; 4] {
    let mut result = [0u8; 4];

    result[0] = ((v.elements[1] as u8) << 4) | (v.elements[0] as u8);
    result[1] = ((v.elements[3] as u8) << 4) | (v.elements[2] as u8);
    result[2] = ((v.elements[5] as u8) << 4) | (v.elements[4] as u8);
    result[3] = ((v.elements[7] as u8) << 4) | (v.elements[6] as u8);

    result
}

#[inline(always)]
fn deserialize_4(bytes: &[u8]) -> PortableVector {
    let mut v = ZERO();

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

#[inline(always)]
fn serialize_5(v: PortableVector) -> [u8; 5] {
    let mut result = [0u8; 5];

    result[0] = ((v.elements[1] & 0x7) << 5 | v.elements[0]) as u8;
    result[1] = (((v.elements[3] & 1) << 7) | (v.elements[2] << 2) | (v.elements[1] >> 3)) as u8;
    result[2] = (((v.elements[4] & 0xF) << 4) | (v.elements[3] >> 1)) as u8;
    result[3] = (((v.elements[6] & 0x3) << 6) | (v.elements[5] << 1) | (v.elements[4] >> 4)) as u8;
    result[4] = ((v.elements[7] << 3) | (v.elements[6] >> 2)) as u8;

    result
}

#[inline(always)]
fn deserialize_5(bytes: &[u8]) -> PortableVector {
    let mut v = ZERO();

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

#[inline(always)]
fn serialize_10(v: PortableVector) -> [u8; 10] {
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

#[inline(always)]
fn deserialize_10(bytes: &[u8]) -> PortableVector {
    let mut result = ZERO();

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
fn serialize_11(v: PortableVector) -> [u8; 11] {
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

#[inline(always)]
fn deserialize_11(bytes: &[u8]) -> PortableVector {
    let mut result = ZERO();
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
fn serialize_12(v: PortableVector) -> [u8; 12] {
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

#[inline(always)]
fn deserialize_12(bytes: &[u8]) -> PortableVector {
    let mut re = ZERO();

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

impl Operations for PortableVector {
    fn ZERO() -> Self {
        zero()
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
