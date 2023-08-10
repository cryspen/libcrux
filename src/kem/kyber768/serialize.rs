use crate::kem::kyber768::utils::{bit_vector::BitVector, ring::LittleEndianBitStream};

use crate::kem::kyber768::parameters::{
    KyberPolynomialRingElement, BITS_PER_COEFFICIENT, BYTES_PER_RING_ELEMENT,
    COEFFICIENTS_IN_RING_ELEMENT
};

use crate::kem::kyber768::field_element::KyberFieldElement;

pub fn serialize_little_endian_1(re: KyberPolynomialRingElement) -> [u8; COEFFICIENTS_IN_RING_ELEMENT / 8] {
    let mut serialized = [0u8; COEFFICIENTS_IN_RING_ELEMENT / 8];

    for (i, chunk) in re.coefficients.chunks_exact(8).enumerate() {
        for (j, coefficient) in chunk.iter().enumerate() {
            serialized[i] |= (coefficient.value as u8) << j
        }
    }

    serialized
}

pub fn serialize_little_endian_4(re: KyberPolynomialRingElement) -> [u8; (COEFFICIENTS_IN_RING_ELEMENT * 4) / 8] {
    let mut serialized = [0u8; (COEFFICIENTS_IN_RING_ELEMENT * 4) / 8];

    for (i, chunk) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient1 = chunk[0].value as u8;
        let coefficient2 = chunk[1].value as u8;

        serialized[i] = (coefficient2 << 4) | coefficient1;
    }

    serialized
}

pub fn serialize_little_endian_10(re: KyberPolynomialRingElement) -> [u8; (COEFFICIENTS_IN_RING_ELEMENT * 10) / 8] {
    let mut serialized = [0u8; (COEFFICIENTS_IN_RING_ELEMENT * 10) / 8];

    for (i, chunk) in re.coefficients.chunks_exact(4).enumerate() {
        let coefficient1 = chunk[0].value;
        let coefficient2 = chunk[1].value;
        let coefficient3 = chunk[2].value;
        let coefficient4 = chunk[3].value;

        serialized[5 * i] = (coefficient1 & 0xFF) as u8;
        serialized[5 * i + 1] = ((coefficient2 & 0x3F) as u8) << 2 | ((coefficient1 >> 8) & 0x03) as u8;
        serialized[5 * i + 2] = ((coefficient3 & 0x0F) as u8) << 4 | ((coefficient2 >> 6) & 0x0F) as u8;
        serialized[5 * i + 3] = ((coefficient4 & 0x03) as u8) << 6 | ((coefficient3 >> 4) & 0x3F) as u8;
        serialized[5 * i + 4] = ((coefficient4 >> 2) & 0xFF) as u8;
    }

    serialized
}

pub fn serialize_little_endian_12(re: KyberPolynomialRingElement) -> [u8; BYTES_PER_RING_ELEMENT] {
    let mut serialized = [0u8; BYTES_PER_RING_ELEMENT];

    for (i, chunks) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient1 = chunks[0].value;
        let coefficient2 = chunks[1].value;

        serialized[3 * i] = (coefficient1 & 0xFF) as u8;
        serialized[3 * i + 1] = ((coefficient1 >> 8) | ((coefficient2 & 0xF) << 4)) as u8;
        serialized[3 * i + 2] = ((coefficient2 >> 4) & 0xFF) as u8;
    }

    serialized
}

fn field_element_from_little_endian_bit_vector(bit_vector: BitVector) -> KyberFieldElement {
    let mut value: u16 = 0;
    for (i, bit) in bit_vector.into_iter().enumerate() {
        value |= u16::from(bit) << i;
    }

    KyberFieldElement {
        value
    }
}

pub fn deserialize_little_endian(
    bits_per_coefficient: usize,
    ring_element_bytes: &[u8],
) -> KyberPolynomialRingElement {
    assert!(bits_per_coefficient <= BITS_PER_COEFFICIENT);

    // FIXME: rewrite like serialization without the `BitVector`.
    let ring_element_bits: BitVector = ring_element_bytes.into();
    let mut ring_element_bits = ring_element_bits.chunks(bits_per_coefficient);

    let mut deserialized = KyberPolynomialRingElement::ZERO;

    for i in 0..deserialized.len() {
        deserialized[i] =
            field_element_from_little_endian_bit_vector(ring_element_bits.next().unwrap());
    }

    deserialized
}
