use super::{
    arithmetic::{get_n_least_significant_bits, FieldElement},
    constants::FIELD_MODULUS,
};

// The approach used in this function been taken from:
// https://github.com/cloudflare/circl/blob/main/pke/kyber/internal/common/poly.go#L150
#[cfg_attr(hax, hax_lib_macros::requires(fe < (FIELD_MODULUS as u16)))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result|
        hax_lib::implies(833 <= fe && fe <= 2596, || result == 1) &&
        hax_lib::implies(!(833 <= fe && fe <= 2596), || result == 0)
))]
pub(super) fn compress_message_coefficient(fe: u16) -> u8 {
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

    // If x <= 831, then x - 832 <= -1 => x - 832 < 0.
    ((shifted_positive_in_range >> 15) & 1) as u8
}

#[cfg_attr(hax,
    hax_lib_macros::requires(
        (coefficient_bits == 4 ||
         coefficient_bits == 5 ||
         coefficient_bits == 10 ||
         coefficient_bits == 11) &&
         fe < (FIELD_MODULUS as u16)))]
#[cfg_attr(hax,
     hax_lib_macros::ensures(
     |result| result >= 0 && result < 2i32.pow(coefficient_bits as u32)))]
pub(super) fn compress_ciphertext_coefficient(coefficient_bits: u8, fe: u16) -> FieldElement {
    hax_lib::debug_assert!(
        coefficient_bits == 4
            || coefficient_bits == 5
            || coefficient_bits == 10
            || coefficient_bits == 11
    );
    hax_lib::debug_assert!(fe <= (FIELD_MODULUS as u16));

    let mut compressed = (fe as u32) << (coefficient_bits + 1);
    compressed += FIELD_MODULUS as u32;

    // N.B.: This division is not constant time since FIELD_MODULUS is prime.
    // This is fine since we're compressing the coefficients of a public value
    // (i.e. the ciphertext)
    compressed /= (FIELD_MODULUS << 1) as u32;

    get_n_least_significant_bits(coefficient_bits, compressed) as FieldElement
}

#[cfg_attr(hax, hax_lib_macros::requires((fe == 0) || (fe == 1)))]
#[inline(always)]
pub(super) fn decompress_message_coefficient(fe: FieldElement) -> FieldElement {
    -fe & ((FIELD_MODULUS + 1) / 2)
}

#[cfg_attr(hax, hax_lib_macros::requires((coefficient_bits == 4 || coefficient_bits == 5 || coefficient_bits == 10 || coefficient_bits == 11) && (fe >= 0) && (fe < 2i32.pow(coefficient_bits as u32))))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result < FIELD_MODULUS))]
pub(super) fn decompress_ciphertext_coefficient(
    coefficient_bits: u8,
    fe: FieldElement,
) -> FieldElement {
    hax_lib::debug_assert!(
        coefficient_bits == 4
            || coefficient_bits == 5
            || coefficient_bits == 10
            || coefficient_bits == 11
    );
    hax_lib::debug_assert!(fe >= 0 && fe <= 2i32.pow(coefficient_bits as u32));

    let mut decompressed = (fe as u32) * (FIELD_MODULUS as u32);
    decompressed = (decompressed << 1) + (1 << coefficient_bits);
    decompressed >>= coefficient_bits + 1;

    decompressed as FieldElement
}
