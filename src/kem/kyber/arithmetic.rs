use super::constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

// if this is 'x'
// let 'fe' be the shorthand for this type
pub(crate) type StandardFieldElement = i32;

// this is congruent to xR^{-1} mod FIELD_MODULUS
// let 'mfe' be the shorthand for this type
pub(crate) type MontgomeryFieldElement = i32;

// this is congruent to xR mod FIELD_MODULUS
// let 'fer' be the shorthand for this type
pub(crate) type FieldElementTimesMontgomeryR = i32;

const MONTGOMERY_SHIFT: u8 = 16;
const MONTGOMERY_R: i32 = 1 << MONTGOMERY_SHIFT;

#[cfg_attr(hax, hax_lib_macros::ensures(|result| result < 2u32.pow(MONTGOMERY_SHIFT as u32)))]
#[inline(always)]
fn get_montgomery_r_least_significant_bits(value: u32) -> u32 {
    value & ((1 << MONTGOMERY_SHIFT) - 1)
}

const BARRETT_SHIFT: i64 = 26;
const BARRETT_R: i64 = 1 << BARRETT_SHIFT;
const BARRETT_MULTIPLIER: i64 = 20159; // floor((BARRETT_R / FIELD_MODULUS) + 0.5)

#[cfg_attr(hax, hax_lib_macros::requires((i64::from(value) > -BARRETT_R && i64::from(value) < BARRETT_R)))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS))]
pub(crate) fn barrett_reduce(value: StandardFieldElement) -> StandardFieldElement {
    hax_lib::debug_assert!(
        i64::from(value) > -BARRETT_R && i64::from(value) < BARRETT_R,
        "value is {value}"
    );

    let t = (i64::from(value) * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    let quotient = (t >> BARRETT_SHIFT) as i32;

    let result = value - (quotient * FIELD_MODULUS);

    hax_lib::debug_assert!(
        result > -FIELD_MODULUS && result < FIELD_MODULUS,
        "value is {value}"
    );

    result
}

const INVERSE_OF_MODULUS_MOD_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R

#[cfg_attr(hax, hax_lib_macros::requires(value >= -FIELD_MODULUS * MONTGOMERY_R && value <= FIELD_MODULUS * MONTGOMERY_R))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result >= -(3 * FIELD_MODULUS) / 2 && result <= (3 * FIELD_MODULUS) / 2))]
pub(crate) fn montgomery_reduce(value: StandardFieldElement) -> StandardFieldElement {
    // This forces hax to extract code for MONTGOMERY_R before it extracts code
    // for this function. The removal of this line is being tracked in:
    // https://github.com/cryspen/libcrux/issues/134
    let _ = MONTGOMERY_R;

    hax_lib::debug_assert!(
        value >= -FIELD_MODULUS * MONTGOMERY_R && value <= FIELD_MODULUS * MONTGOMERY_R,
        "value is {value}"
    );

    let t = get_montgomery_r_least_significant_bits(value as u32) * INVERSE_OF_MODULUS_MOD_R;
    let k = get_montgomery_r_least_significant_bits(t) as i16;

    let k_times_modulus = (k as i32) * FIELD_MODULUS;

    let c = k_times_modulus >> MONTGOMERY_SHIFT;
    let value_high = value >> MONTGOMERY_SHIFT;

    value_high - c
}

pub(crate) fn montgomery_multiply_sfe_by_fer(
    fe: StandardFieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> StandardFieldElement {
    montgomery_reduce(fe * fer)
}

pub(crate) fn to_standard_domain(mfe: MontgomeryFieldElement) -> StandardFieldElement {
    montgomery_reduce(mfe * 1353)
}

#[cfg_attr(hax, hax_lib_macros::requires(fe >= -FIELD_MODULUS && fe < FIELD_MODULUS))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result >= 0 && result < (FIELD_MODULUS as u16)))]
#[inline(always)]
pub(crate) fn to_unsigned_representative(fe: StandardFieldElement) -> u16 {
    hax_lib::debug_assert!(fe >= -FIELD_MODULUS && fe < FIELD_MODULUS);
    (fe + (FIELD_MODULUS & (fe >> 31))) as u16
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PolynomialRingElement {
    pub(crate) coefficients: [StandardFieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl PolynomialRingElement {
    pub const ZERO: Self = Self {
        coefficients: [0i32; 256], // FIXME: hax issue, this is COEFFICIENTS_IN_RING_ELEMENT
    };
}

pub(crate) fn add_to_ring_element<const K: usize>(
    mut lhs: PolynomialRingElement,
    rhs: &PolynomialRingElement,
) -> PolynomialRingElement {
    hax_lib::debug_assert!(lhs.coefficients.into_iter().all(|coefficient| coefficient
        >= ((K as i32) - 1) * -FIELD_MODULUS
        && coefficient <= ((K as i32) - 1) * FIELD_MODULUS));
    hax_lib::debug_assert!(rhs
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient >= -FIELD_MODULUS && coefficient <= FIELD_MODULUS));

    for i in 0..lhs.coefficients.len() {
        lhs.coefficients[i] += rhs.coefficients[i];
    }

    hax_lib::debug_assert!(lhs
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient >= (K as i32) * -FIELD_MODULUS
            && coefficient <= (K as i32) * FIELD_MODULUS));
    lhs
}
