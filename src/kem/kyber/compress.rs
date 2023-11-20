use super::{arithmetic::StandardFieldElement, constants::FIELD_MODULUS};

#[cfg_attr(hax, hax_lib_macros::requires(n > 0 && n <= 11))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result < 2u32.pow(n.into())))]
#[inline(always)]
fn get_n_least_significant_bits(n: u8, value: u32) -> u32 {
    hax_lib::debug_assert!(n > 0 && n <= 11);

    value & ((1 << n) - 1)
}

#[cfg_attr(hax, hax_lib_macros::requires(coefficient_bits > 0 && coefficient_bits <= 11 && fe <= (FIELD_MODULUS as u16)))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result >= 0 && result < 2i32.pow(coefficient_bits as u32)))]
pub(super) fn compress_q(coefficient_bits: u8, fe: u16) -> StandardFieldElement {
    hax_lib::debug_assert!(coefficient_bits > 0 && coefficient_bits <= 11);
    hax_lib::debug_assert!(fe <= (FIELD_MODULUS as u16));

    let mut compressed = (fe as u32) << (coefficient_bits + 1);
    compressed += FIELD_MODULUS as u32;
    compressed /= (FIELD_MODULUS << 1) as u32;

    get_n_least_significant_bits(coefficient_bits, compressed) as StandardFieldElement
}

#[cfg_attr(hax, hax_lib_macros::requires(coefficient_bits > 0 && coefficient_bits <= 11 && (fe >= 0) && (fe < 2i32.pow(coefficient_bits as u32))))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result < FIELD_MODULUS))]
pub(super) fn decompress_q(coefficient_bits: u8, fe: StandardFieldElement) -> StandardFieldElement {
    hax_lib::debug_assert!(coefficient_bits > 0 && coefficient_bits <= 11);
    hax_lib::debug_assert!(fe >= 0 && fe <= 2i32.pow(coefficient_bits as u32));

    let mut decompressed = (fe as u32) * (FIELD_MODULUS as u32);
    decompressed = (decompressed << 1) + (1 << coefficient_bits);
    decompressed >>= coefficient_bits + 1;

    decompressed as StandardFieldElement
}
