use crate::constants::FIELD_MODULUS;
use crate::hax_utils::hax_debug_assert;

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i16;

pub(crate) const MONTGOMERY_SHIFT: u8 = 16;
pub(crate) const MONTGOMERY_R: i32 = 1 << MONTGOMERY_SHIFT;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R^(-1) (mod FIELD_MODULUS).
/// We use 'mfe' as a shorthand for this type
pub(crate) type MontgomeryFieldElement = i16;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub(crate) type FieldElementTimesMontgomeryR = i16;

#[cfg_attr(hax, hax_lib::requires(n == 4 || n == 5 || n == 10 || n == 11 || n == MONTGOMERY_SHIFT))]
#[cfg_attr(hax, hax_lib::ensures(|result| result < 2u32.pow(n.into())))]
#[inline(always)]
pub(crate) fn get_n_least_significant_bits(n: u8, value: u32) -> u32 {
    hax_debug_assert!(n == 4 || n == 5 || n == 10 || n == 11 || n == MONTGOMERY_SHIFT);

    value & ((1 << n) - 1)
}

pub(crate) const BARRETT_SHIFT: i32 = 26;
pub(crate) const BARRETT_R: i32 = 1 << BARRETT_SHIFT;

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
pub(crate) const BARRETT_MULTIPLIER: i32 = 20159;

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

#[cfg_attr(hax, hax_lib::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS))]
pub(crate) fn barrett_reduce(value: i16) -> FieldElement {
    let t = (value as i32 * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    let quotient = (t >> BARRETT_SHIFT) as i16;

    let result = value - (quotient * FIELD_MODULUS);

    hax_debug_assert!(
        result > -FIELD_MODULUS && result < FIELD_MODULUS,
        "value is {value}"
    );

    result
}

pub(crate) const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: i32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R

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
pub(crate) fn montgomery_reduce(value: i32) -> MontgomeryFieldElement {
    // This forces hax to extract code for MONTGOMERY_R before it extracts code
    // for this function. The removal of this line is being tracked in:
    // https://github.com/cryspen/libcrux/issues/134
    let _ = MONTGOMERY_R;

    hax_debug_assert!(
        value >= -FIELD_MODULUS * MONTGOMERY_R && value <= FIELD_MODULUS * MONTGOMERY_R,
        "value is {value}"
    );

    let k = (value as i16) as i32 * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    let k_times_modulus = (k as i16 as i32) * (FIELD_MODULUS as i32);

    let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    let value_high = (value >> MONTGOMERY_SHIFT) as i16;

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
    montgomery_reduce(fe as i32 * (fer as i32))
}

/// This is calculated as (MONTGOMERY_R)^2 mod FIELD_MODULUS
pub(crate) const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353;

/// If x is some field element of the Kyber field and `mfe` is congruent to
/// x · MONTGOMERY_R^{-1}, this procedure outputs a value that is congruent to
/// `x`, as follows:
///
///    mfe · MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS ≡ x · MONTGOMERY_R^{-1} * (MONTGOMERY_R)^2 (mod FIELD_MODULUS)
/// => mfe · MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS ≡ x · MONTGOMERY_R (mod FIELD_MODULUS)
///
/// `montgomery_reduce` takes the value `x · MONTGOMERY_R` and outputs a representative
/// `x · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x (mod FIELD_MODULUS)`
#[inline(always)]
pub(crate) fn _to_standard_domain(mfe: MontgomeryFieldElement) -> FieldElement {
    montgomery_reduce(mfe as i32 * (MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS as i32))
}

/// Given a field element `fe` such that -FIELD_MODULUS ≤ fe < FIELD_MODULUS,
/// output `o` such that:
/// - `o` is congruent to `fe`
/// - 0 ≤ `o` FIELD_MODULUS
#[cfg_attr(hax, hax_lib::requires(fe >= -FIELD_MODULUS && fe < FIELD_MODULUS))]
#[cfg_attr(hax, hax_lib::ensures(|result| result >= 0 && result < (FIELD_MODULUS as u16)))]
#[inline(always)]
pub(crate) fn _to_unsigned_representative(fe: FieldElement) -> u16 {
    hax_debug_assert!(fe >= -FIELD_MODULUS && fe < FIELD_MODULUS);
    (fe + (FIELD_MODULUS & (fe >> 15))) as u16
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
        montgomery_reduce(a0 as i32 * b0 as i32 + montgomery_reduce(a1 as i32 * b1 as i32) as i32 * zeta as i32),
        montgomery_reduce(a0 as i32 * b1 as i32 + a1 as i32 * b0 as i32),
    )
}
