use crate::kyber768::parameters::{self, KyberFieldElement, KyberPolynomialRingElement};

pub fn compress(
    re: KyberPolynomialRingElement,
    bits_per_compressed_coefficient: usize,
) -> KyberPolynomialRingElement {
    KyberPolynomialRingElement::new(
        re.coefficients()
            .map(|coefficient| compress_q(coefficient, bits_per_compressed_coefficient)),
    )
}

pub fn decompress(
    re: KyberPolynomialRingElement,
    bits_per_compressed_coefficient: usize,
) -> KyberPolynomialRingElement {
    KyberPolynomialRingElement::new(
        re.coefficients()
            .map(|coefficient| decompress_q(coefficient, bits_per_compressed_coefficient)),
    )
}

fn compress_q(fe: KyberFieldElement, to_bit_size: usize) -> KyberFieldElement {
    assert!(to_bit_size <= parameters::BITS_PER_COEFFICIENT);

    let two_pow_bit_size = 2u32.pow(to_bit_size.try_into().unwrap_or_else(|_| {
        panic!(
            "Conversion should work since to_bit_size is never greater than {}.",
            parameters::BITS_PER_COEFFICIENT
        )
    }));

    let compressed = ((u32::from(fe.value) * 2 * two_pow_bit_size)
        + u32::from(KyberFieldElement::MODULUS))
        / u32::from(2 * KyberFieldElement::MODULUS);

    (compressed % two_pow_bit_size).into()
}

fn decompress_q(fe: KyberFieldElement, to_bit_size: usize) -> KyberFieldElement {
    assert!(to_bit_size <= parameters::BITS_PER_COEFFICIENT);

    let decompressed = (2 * u32::from(fe.value) * u32::from(KyberFieldElement::MODULUS)
        + (1 << to_bit_size))
        >> (to_bit_size + 1);

    decompressed.into()
}
