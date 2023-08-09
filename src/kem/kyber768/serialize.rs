use crate::kem::kyber768::utils::{bit_vector::BitVector, ring::LittleEndianBitStream};

use crate::kem::kyber768::parameters::{
    KyberFieldElement, KyberPolynomialRingElement, BITS_PER_COEFFICIENT, BYTES_PER_RING_ELEMENT,
};

pub fn serialize_little_endian(
    re: KyberPolynomialRingElement,
    bits_per_coefficient: usize,
) -> Vec<u8> {
    let out_bytes = (re.coefficients.len() * bits_per_coefficient) / 8;
    let mut serialized: Vec<u8> = Vec::with_capacity(out_bytes);

    for i in 0..out_bytes {
        let mut byte_value: u8 = 0;

        for bit_pos in 0..8 {
            let bit = re
                .coefficients()
                .nth_bit_with_coefficient_bit_size(i * 8 + bit_pos, bits_per_coefficient);
            byte_value |= bit << bit_pos;
        }

        serialized.push(byte_value);
    }

    serialized
}

pub fn serialize_little_endian_12(re: KyberPolynomialRingElement) -> [u8; BYTES_PER_RING_ELEMENT] {
    let mut serialized = [0u8; BYTES_PER_RING_ELEMENT];

    for (i, chunks) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient_1 = chunks[0].value;
        let coefficient_2 = chunks[1].value;

        serialized[3 * i] = (coefficient_1 & 0xFF) as u8;
        serialized[3 * i + 1] = ((coefficient_1 >> 8) | ((coefficient_2 & 0xF) << 4)) as u8;
        serialized[3 * i + 2] = ((coefficient_2 >> 4) & 0xFF) as u8;
    }

    serialized
}

fn field_element_from_little_endian_bit_vector(bit_vector: BitVector) -> KyberFieldElement {
    let mut value: u16 = 0;
    for (i, bit) in bit_vector.into_iter().enumerate() {
        value |= u16::from(bit) << i;
    }

    value.into()
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
