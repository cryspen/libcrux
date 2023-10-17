use super::{
    arithmetic::{KyberFieldElement, KyberPolynomialRingElement},
    constants::{BITS_PER_COEFFICIENT, FIELD_MODULUS},
    conversions::to_unsigned_representative,
};

pub(crate) fn compress_q<const COEFFICIENT_BITS: usize>(fe: u16) -> KyberFieldElement {
    debug_assert!(COEFFICIENT_BITS <= BITS_PER_COEFFICIENT);

    let mut compressed = (fe as u32) << (COEFFICIENT_BITS + 1);
    compressed += FIELD_MODULUS as u32;
    compressed /= (FIELD_MODULUS << 1) as u32;

    (compressed & ((1u32 << COEFFICIENT_BITS) - 1)) as KyberFieldElement
}
pub fn compress<const COEFFICIENT_BITS: usize>(
    mut re: KyberPolynomialRingElement,
) -> KyberPolynomialRingElement {
    re.coefficients = re
        .coefficients
        .map(|coefficient| compress_q::<COEFFICIENT_BITS>(to_unsigned_representative(coefficient)));
    re
}

fn decompress_q<const COEFFICIENT_BITS: usize>(fe: KyberFieldElement) -> KyberFieldElement {
    debug_assert!(COEFFICIENT_BITS <= BITS_PER_COEFFICIENT);

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
