use crate::hax_utils::hax_debug_assert;

use super::{
    arithmetic::{get_n_least_significant_bits, FieldElement},
    constants::FIELD_MODULUS,
};

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

#[cfg_attr(hax, hax_lib::requires(fe < (FIELD_MODULUS as u16)))]
#[cfg_attr(hax, hax_lib::ensures(|result|
        hax_lib::implies(833 <= fe && fe <= 2596, || result == 1) &&
        hax_lib::implies(!(833 <= fe && fe <= 2596), || result == 0)
))]
pub(super) fn compress_message_coefficient(fe: u16) -> u8 {
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
         fe < (FIELD_MODULUS as u16)))]
#[cfg_attr(hax,
     hax_lib::ensures(
     |result| result >= 0 && result < 2i32.pow(coefficient_bits as u32)))]
pub(super) fn compress_ciphertext_coefficient(coefficient_bits: u8, fe: u16) -> FieldElement {
    hax_debug_assert!(
        coefficient_bits == 4
            || coefficient_bits == 5
            || coefficient_bits == 10
            || coefficient_bits == 11
    );
    hax_debug_assert!(fe <= (FIELD_MODULUS as u16));

    // This has to be constant time due to:
    // https://groups.google.com/a/list.nist.gov/g/pqc-forum/c/ldX0ThYJuBo/m/ovODsdY7AwAJ
    let mut compressed = (fe as u64) << coefficient_bits;
    compressed += 1664 as u64;

    compressed *= 10_321_340;
    compressed >>= 35;

    get_n_least_significant_bits(coefficient_bits, compressed as u32) as FieldElement
}

/// The `decompress_*` functions implement the `Decompress` function specified in the NIST FIPS
/// 203 standard (Page 18, Expression 4.6), which is defined as:
///
/// ```plaintext
/// Decompress_d: ℤ_{2ᵈ} -> ℤq
/// Decompress_d(y) = ⌈(q/2ᵈ)·y⌋
/// ```
///
/// Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
///
/// ```plaintext
/// Decompress_d(y) = ⌊(q/2ᵈ)·y + 1/2⌋
///                 = ⌊(2·y·q + 2ᵈ) / 2^{d+1})⌋
/// ```
///
/// For further information about the function implementations, consult the
/// `implementation_notes.pdf` document in this directory.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.

#[cfg_attr(hax, hax_lib::requires((fe == 0) || (fe == 1)))]
#[inline(always)]
pub(super) fn decompress_message_coefficient(fe: FieldElement) -> FieldElement {
    -fe & ((FIELD_MODULUS + 1) / 2)
}

#[cfg_attr(hax, hax_lib::requires((coefficient_bits == 4 || coefficient_bits == 5 || coefficient_bits == 10 || coefficient_bits == 11) && (fe >= 0) && (fe < 2i32.pow(coefficient_bits as u32))))]
#[cfg_attr(hax, hax_lib::ensures(|result| result < FIELD_MODULUS))]
pub(super) fn decompress_ciphertext_coefficient(
    coefficient_bits: u8,
    fe: FieldElement,
) -> FieldElement {
    hax_debug_assert!(
        coefficient_bits == 4
            || coefficient_bits == 5
            || coefficient_bits == 10
            || coefficient_bits == 11
    );
    hax_debug_assert!(fe >= 0 && fe <= 2i32.pow(coefficient_bits as u32));

    let mut decompressed = (fe as u32) * (FIELD_MODULUS as u32);
    decompressed = (decompressed << 1) + (1 << coefficient_bits);
    decompressed >>= coefficient_bits + 1;

    decompressed as FieldElement
}
