use crate::helpers::bit_vector::BitVector;
use crate::parameters::KyberFieldElement;
use crate::parameters::KyberPolynomialRingElement;

impl KyberFieldElement {
    pub fn new_from_bit_vector(bit_vector: BitVector) -> Self {
        let mut value: u16 = 0;
        for (i, bit) in bit_vector.into_iter().enumerate() {
            value |= u16::from(bit) << i;
        }

        value.into()
    }

    pub fn as_bit_vector(&self, bits_to_represent_value: usize) -> BitVector {
        let mut bits: Vec<u8> = Vec::new();

        for i in 0..bits_to_represent_value {
            bits.push(((self.value >> i) & 1).try_into().unwrap());
        }

        BitVector::new(bits)
    }
}

impl KyberPolynomialRingElement {
    fn as_bit_vector(&self, bits_per_coefficient: usize) -> Vec<u8> {
        let mut ring_element_bits: Vec<u8> = Vec::new();

        for coefficient in self.coefficients {
            for bit in coefficient.as_bit_vector(bits_per_coefficient).into_iter() {
                ring_element_bits.push(bit);
            }
        }

        ring_element_bits
    }

    pub fn serialize(&self, bits_per_coefficient: usize) -> Vec<u8> {
        let mut serialized: Vec<u8> = Vec::new();

        for bit_vector in self.as_bit_vector(bits_per_coefficient).chunks(8) {
            let mut byte_value: u8 = 0;
            for (i, bit) in bit_vector.iter().enumerate() {
                byte_value |= *bit << i;
            }

            serialized.push(byte_value);
        }

        serialized
    }

    pub fn new_from_bytes(bits_per_coefficient: usize, serialized: &[u8]) -> Self {
        assert!(bits_per_coefficient <= 12);

        let serialized_bits: BitVector = serialized.into();
        let mut serialized_bits = serialized_bits.chunks(bits_per_coefficient);

        let mut deserialized = KyberPolynomialRingElement::ZERO;

        for i in 0..deserialized.coefficients.len() {
            deserialized.coefficients[i] =
                KyberFieldElement::new_from_bit_vector(serialized_bits.next().unwrap());
        }

        deserialized
    }
}
