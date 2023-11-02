use super::{
    arithmetic::{KyberFieldElement, KyberPolynomialRingElement},
    constants::FIELD_MODULUS,
};

#[cfg_attr(hax, hax_lib_macros::requires(COEFFICIENT_BITS <= 11 && i32::from(fe) <= FIELD_MODULUS))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result >= 0 && result <= (1 << COEFFICIENT_BITS) - 1))]
pub(super) fn compress_q<const COEFFICIENT_BITS: usize>(fe: u16) -> KyberFieldElement {
    let mut compressed = (fe as u32) << (COEFFICIENT_BITS + 1);
    compressed += FIELD_MODULUS as u32;
    compressed /= (FIELD_MODULUS << 1) as u32;

    (compressed & ((1u32 << COEFFICIENT_BITS) - 1)) as KyberFieldElement
}

#[cfg_attr(hax, hax_lib_macros::requires(COEFFICIENT_BITS <= 11 && (fe >= 0) && (fe < (1 << COEFFICIENT_BITS))))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result| result < FIELD_MODULUS))]
pub(super) fn decompress_q<const COEFFICIENT_BITS: usize>(
    fe: KyberFieldElement,
) -> KyberFieldElement {
    let mut decompressed = (fe as u32) * (FIELD_MODULUS as u32);
    decompressed = (decompressed << 1) + (1 << COEFFICIENT_BITS);
    decompressed >>= COEFFICIENT_BITS + 1;

    decompressed as KyberFieldElement
}
pub fn decompress<const COEFFICIENT_BITS: usize>(
    mut re: KyberPolynomialRingElement,
) -> KyberPolynomialRingElement {
    re.coefficients = re
        .coefficients
        .map(|coefficient| decompress_q::<COEFFICIENT_BITS>(coefficient));
    re
}
