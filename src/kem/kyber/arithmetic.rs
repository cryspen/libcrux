use crate::hax_utils::hax_debug_assert;

use super::constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

/// Values having this type hold a representative 'x' of the Kyber Field.
/// Let 'fe' be the shorthand for this type
pub(crate) type FieldElement = i32;

/// Values having this type hold a representative y ≡ xR^{-1} (mod FIELD_MODULUS)
/// Let 'mfe' be the shorthand for this type
pub(crate) type MontgomeryFieldElement = i32;

/// Values having this type hold a representative y ≡ xR (mod FIELD_MODULUS)
/// Let 'fer' be the shorthand for this type
pub(crate) type FieldElementTimesMontgomeryR = i32;

const MONTGOMERY_SHIFT: u8 = 16;
const MONTGOMERY_R: i32 = 1 << MONTGOMERY_SHIFT;

#[cfg_attr(hax, hax_lib_macros::requires(n == 4 || n == 5 || n == 10 || n == 11 || n == MONTGOMERY_SHIFT))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result < 2u32.pow(n.into())))]
#[inline(always)]
pub(crate) fn get_n_least_significant_bits(n: u8, value: u32) -> u32 {
    hax_debug_assert!(n == 4 || n == 5 || n == 10 || n == 11 || n == MONTGOMERY_SHIFT);

    value & ((1 << n) - 1)
}

const BARRETT_SHIFT: i64 = 26;
const BARRETT_R: i64 = 1 << BARRETT_SHIFT;
const BARRETT_MULTIPLIER: i64 = 20159; // floor((BARRETT_R / FIELD_MODULUS) + 0.5)

#[cfg_attr(hax, hax_lib_macros::requires((i64::from(value) > -BARRETT_R && i64::from(value) < BARRETT_R)))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS))]
pub(crate) fn barrett_reduce(value: FieldElement) -> FieldElement {
    hax_debug_assert!(
        i64::from(value) > -BARRETT_R && i64::from(value) < BARRETT_R,
        "value is {value}"
    );

    let t = (i64::from(value) * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    let quotient = (t >> BARRETT_SHIFT) as i32;

    let result = value - (quotient * FIELD_MODULUS);

    hax_debug_assert!(
        result > -FIELD_MODULUS && result < FIELD_MODULUS,
        "value is {value}"
    );

    result
}

const INVERSE_OF_MODULUS_MOD_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R

#[cfg_attr(hax, hax_lib_macros::requires(value >= -FIELD_MODULUS * MONTGOMERY_R && value <= FIELD_MODULUS * MONTGOMERY_R))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result >= -(3 * FIELD_MODULUS) / 2 && result <= (3 * FIELD_MODULUS) / 2))]
pub(crate) fn montgomery_reduce(value: FieldElement) -> FieldElement {
    // This forces hax to extract code for MONTGOMERY_R before it extracts code
    // for this function. The removal of this line is being tracked in:
    // https://github.com/cryspen/libcrux/issues/134
    let _ = MONTGOMERY_R;

    hax_debug_assert!(
        value >= -FIELD_MODULUS * MONTGOMERY_R && value <= FIELD_MODULUS * MONTGOMERY_R,
        "value is {value}"
    );

    let t = get_n_least_significant_bits(MONTGOMERY_SHIFT, value as u32) * INVERSE_OF_MODULUS_MOD_R;
    let k = get_n_least_significant_bits(MONTGOMERY_SHIFT, t) as i16;

    let k_times_modulus = (k as i32) * FIELD_MODULUS;

    let c = k_times_modulus >> MONTGOMERY_SHIFT;
    let value_high = value >> MONTGOMERY_SHIFT;

    value_high - c
}

#[inline(always)]
pub(crate) fn montgomery_multiply_sfe_by_fer(
    fe: FieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> FieldElement {
    montgomery_reduce(fe * fer)
}

const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i32 = 1353; // (MONTGOMERY_R)^2 mod FIELD_MODULUS

#[inline(always)]
pub(crate) fn to_standard_domain(mfe: MontgomeryFieldElement) -> FieldElement {
    montgomery_reduce(mfe * MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS)
}

#[cfg_attr(hax, hax_lib_macros::requires(fe >= -FIELD_MODULUS && fe < FIELD_MODULUS))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result >= 0 && result < (FIELD_MODULUS as u16)))]
#[inline(always)]
pub(crate) fn to_unsigned_representative(fe: FieldElement) -> u16 {
    hax_debug_assert!(fe >= -FIELD_MODULUS && fe < FIELD_MODULUS);
    (fe + (FIELD_MODULUS & (fe >> 31))) as u16
}

#[derive(Clone, Copy)]
pub struct PolynomialRingElement {
    pub(crate) coefficients: [FieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl PolynomialRingElement {
    pub const ZERO: Self = Self {
        coefficients: [0i32; 256], // FIXME: hax issue, this is COEFFICIENTS_IN_RING_ELEMENT
    };
}

#[cfg_attr(hax, hax_lib_macros::requires(
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < COEFFICIENTS_IN_RING_ELEMENT, ||
            (lhs.coefficients[i].abs() <= ((K as i32) - 1) * FIELD_MODULUS) &&
            (rhs.coefficients[i].abs() <= FIELD_MODULUS)

))))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result|
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < result.coefficients.len(), ||
                result.coefficients[i].abs() <= (K as i32) * FIELD_MODULUS
))))]
pub(crate) fn add_to_ring_element<const K: usize>(
    mut lhs: PolynomialRingElement,
    rhs: &PolynomialRingElement,
) -> PolynomialRingElement {
    hax_debug_assert!(lhs
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() <= ((K as i32) - 1) * FIELD_MODULUS));
    hax_debug_assert!(rhs
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() < FIELD_MODULUS));

    for i in 0..lhs.coefficients.len() {
        lhs.coefficients[i] += rhs.coefficients[i];
    }

    hax_debug_assert!(lhs
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() <= (K as i32) * FIELD_MODULUS));

    lhs
}
