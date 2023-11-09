use super::constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

pub(crate) type KyberFieldElement = i32;

const MONTGOMERY_SHIFT: u8 = 16;
const MONTGOMERY_R: i32 = 1 << MONTGOMERY_SHIFT;

#[cfg_attr(hax, hax_lib_macros::ensures(|result| result < 2u16.pow(MONTGOMERY_SHIFT as u32)))]
#[inline(always)]
fn get_montgomery_r_least_significant_bits(value: i32) -> u16 {
    (value & ((1 << MONTGOMERY_SHIFT) - 1)) as u16
}

const BARRETT_SHIFT: i64 = 26;
const BARRETT_R: i64 = 1 << BARRETT_SHIFT;
const BARRETT_MULTIPLIER: i64 = 20159; // floor((BARRETT_R / FIELD_MODULUS) + 0.5)

#[cfg_attr(hax, hax_lib_macros::requires((i64::from(value) > -(BARRETT_R / 2) && i64::from(value) < BARRETT_R / 2)))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS))]
pub(crate) fn barrett_reduce(value: KyberFieldElement) -> KyberFieldElement {
    let t = (i64::from(value) * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    let quotient = (t >> BARRETT_SHIFT) as i32;

    value - (quotient * FIELD_MODULUS)
}

const INVERSE_OF_MODULUS_MOD_R: i32 = -3327; // FIELD_MODULUS^{-1} mod MONTGOMERY_R

#[cfg_attr(hax, hax_lib_macros::requires(value >= -FIELD_MODULUS * MONTGOMERY_R && value <= FIELD_MODULUS * MONTGOMERY_R))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result >= -(3 * FIELD_MODULUS) / 2 && result <= (3 * FIELD_MODULUS) / 2))]
pub(crate) fn montgomery_reduce(value: KyberFieldElement) -> KyberFieldElement {
    hax_lib::debug_assert!(
        value >= -FIELD_MODULUS * MONTGOMERY_R && value <= FIELD_MODULUS * MONTGOMERY_R,
        "value is {value}"
    );

    let k = (get_montgomery_r_least_significant_bits(value) as i32) * INVERSE_OF_MODULUS_MOD_R;
    let k = get_montgomery_r_least_significant_bits(k) as i16;

    let c = ((k as i32) * FIELD_MODULUS) >> MONTGOMERY_SHIFT;
    let value_high = value >> MONTGOMERY_SHIFT;

    value_high - c
}

#[cfg_attr(hax, hax_lib_macros::requires(fe >= -FIELD_MODULUS && fe < FIELD_MODULUS))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result >= 0 && result < (FIELD_MODULUS as u16)))]
#[inline(always)]
pub(crate) fn to_unsigned_representative(fe: KyberFieldElement) -> u16 {
    hax_lib::debug_assert!(fe >= -FIELD_MODULUS && fe < FIELD_MODULUS);
    (fe + (FIELD_MODULUS & (fe >> 31))) as u16
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KyberPolynomialRingElement {
    pub(crate) coefficients: [KyberFieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl KyberPolynomialRingElement {
    pub const ZERO: Self = Self {
        coefficients: [0i32; 256], // FIXME: hax issue, this is COEFFICIENTS_IN_RING_ELEMENT
    };
}

pub(crate) fn add_to_ring_element<const K: usize>(
    mut lhs: KyberPolynomialRingElement,
    rhs: &KyberPolynomialRingElement,
) -> KyberPolynomialRingElement {
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
