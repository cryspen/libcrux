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

    let mut compressed = u32::from(fe.value) * (two_pow_bit_size << 1);
    compressed += u32::from(KyberFieldElement::MODULUS);
    compressed /= u32::from(KyberFieldElement::MODULUS << 1);

    KyberFieldElement {
        value: (compressed & (two_pow_bit_size - 1)) as u16,
    }
}

fn decompress_q(fe: KyberFieldElement, to_bit_size: usize) -> KyberFieldElement {
    debug_assert!(to_bit_size <= parameters::BITS_PER_COEFFICIENT);

    let mut decompressed = u32::from(fe.value) * u32::from(KyberFieldElement::MODULUS);
    decompressed = (decompressed << 1) + (1 << to_bit_size);
    decompressed >>= to_bit_size + 1;

    KyberFieldElement {
        value: decompressed as u16,
    }
}
