use crate::kem::kyber768::{
    arithmetic::{KyberFieldElement, KyberPolynomialRingElement},
    parameters::{self, FIELD_MODULUS},
};

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
    debug_assert!(to_bit_size <= parameters::BITS_PER_COEFFICIENT);

    let two_pow_bit_size = 1u32 << to_bit_size;

    let fe = fe + ((fe >> 15) & FIELD_MODULUS);

    let mut compressed = (fe as u32) * (two_pow_bit_size << 1);
    compressed += parameters::FIELD_MODULUS as u32;
    compressed /= (parameters::FIELD_MODULUS << 1) as u32;

    (compressed & (two_pow_bit_size - 1)) as i16
}

fn decompress_q(fe: KyberFieldElement, to_bit_size: usize) -> KyberFieldElement {
    debug_assert!(to_bit_size <= parameters::BITS_PER_COEFFICIENT);

    let mut decompressed = (fe as u32) * (parameters::FIELD_MODULUS as u32);
    decompressed = (decompressed << 1) + (1 << to_bit_size);
    decompressed >>= to_bit_size + 1;

    decompressed as i16
}
