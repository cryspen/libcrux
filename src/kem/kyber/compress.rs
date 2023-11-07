use super::{
    arithmetic::{get_n_least_significant_bits_of_u32, KyberFieldElement},
    constants::FIELD_MODULUS,
};

#[cfg_attr(hax, hax_lib_macros::requires(coefficient_bits > 0 && coefficient_bits <= 11 && fe <= (FIELD_MODULUS as u16)))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result >= 0 && result < 2i32.pow(coefficient_bits as u32)))]
pub(super) fn compress_q(coefficient_bits: u8, fe: u16) -> KyberFieldElement {
    let mut compressed = (fe as u32) << (coefficient_bits + 1);
    compressed += FIELD_MODULUS as u32;
    compressed /= (FIELD_MODULUS << 1) as u32;

    get_n_least_significant_bits_of_u32(coefficient_bits, compressed) as KyberFieldElement
}

#[cfg_attr(hax, hax_lib_macros::requires(coefficient_bits > 0 && coefficient_bits <= 11 && (fe >= 0) && (fe < 2i32.pow(coefficient_bits as u32))))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result < FIELD_MODULUS))]
pub(super) fn decompress_q(coefficient_bits: u8, fe: KyberFieldElement) -> KyberFieldElement {
    let mut decompressed = (fe as u32) * (FIELD_MODULUS as u32);
    decompressed = (decompressed << 1) + (1 << coefficient_bits);
    decompressed >>= coefficient_bits + 1;

    decompressed as KyberFieldElement
}
