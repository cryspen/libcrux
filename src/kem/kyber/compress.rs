use super::{arithmetic::KyberFieldElement, constants::FIELD_MODULUS};

#[cfg_attr(hax, hax_lib_macros::requires(coefficient_bits <= 11 && fe <= (FIELD_MODULUS as u16)))]
//#[cfg_attr(hax, hax_lib_macros::ensures(|result| result >= 0 && result <= (1 << coefficient_bits) - 1))]
pub(super) fn compress_q(coefficient_bits: u32, fe: u16) -> KyberFieldElement {
    let mut compressed = (fe as u32) << (coefficient_bits + 1);
    compressed += FIELD_MODULUS as u32;
    compressed /= (FIELD_MODULUS << 1) as u32;

    (compressed & ((1u32 << coefficient_bits) - 1)) as KyberFieldElement
}

#[cfg_attr(hax, hax_lib_macros::requires(coefficient_bits <= 11 && (fe >= 0) && (fe < (1 << coefficient_bits))))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result < FIELD_MODULUS))]
pub(super) fn decompress_q(coefficient_bits: u32, fe: KyberFieldElement) -> KyberFieldElement {
    let mut decompressed = (fe as u32) * (FIELD_MODULUS as u32);
    decompressed = (decompressed << 1) + (1 << coefficient_bits);
    decompressed >>= coefficient_bits + 1;

    decompressed as KyberFieldElement
}
