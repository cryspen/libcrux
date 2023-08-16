use crate::kem::kyber768::{
    field_element::KyberFieldElement,
    parameters::{self, KyberPolynomialRingElement},
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

    let mut compressed = (fe.value as u32) * (two_pow_bit_size << 1);
    compressed += KyberFieldElement::MODULUS as u32;
    compressed /= (KyberFieldElement::MODULUS << 1) as u32;

    KyberFieldElement {
        value: (compressed & (two_pow_bit_size - 1)) as i16,
    }
}

fn decompress_q(fe: KyberFieldElement, to_bit_size: usize) -> KyberFieldElement {
    debug_assert!(to_bit_size <= parameters::BITS_PER_COEFFICIENT);

    let mut decompressed = (fe.value as u32) * (KyberFieldElement::MODULUS as u32);
    decompressed = (decompressed << 1) + (1 << to_bit_size);
    decompressed >>= to_bit_size + 1;

    KyberFieldElement {
        value: decompressed as i16,
    }
}
