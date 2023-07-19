use crate::helpers;
use crate::parameters::KyberFieldElement;
use crate::parameters::KyberPolynomialRingElement;

impl KyberFieldElement {
    pub fn new_from_bit_vector(bits_to_represent_value : usize, bit_vector : &[u8]) -> Self {
        assert!(bits_to_represent_value <= 12);

        let mut value : u16 = 0;
        for (i, bit) in bit_vector.iter().enumerate() {
            value |= u16::from(*bit) << i;
        }

        Self {
            value,
            bits_to_represent_value
        }
    }

    pub fn as_bit_vector(&self) -> Vec<u8> {
        let mut bit_vector : Vec<u8> = Vec::new();

        for i in 0..self.bits_to_represent_value {
            bit_vector.push(((self.value >> i) & 1).try_into().unwrap());
        }

        bit_vector
    }
}

impl KyberPolynomialRingElement {
    fn as_bit_vector(&self) -> Vec<u8> {
        let mut ring_element_bits : Vec<u8> = Vec::new();

        for coefficient in self.coefficients {
            for bit in coefficient.as_bit_vector().iter() {
                ring_element_bits.push(*bit);
            }
        }

        ring_element_bits
    }

    pub fn serialize(&self) -> Vec<u8> {
        let mut serialized : Vec<u8> = Vec::new();

        for bit_vector in self.as_bit_vector().chunks(8) {
            let mut byte_value: u8 = 0;
            for (i, bit) in bit_vector.iter().enumerate() {
                byte_value |= *bit << i;
            }

            serialized.push(byte_value);
        }

        serialized
    }


    pub fn new_from_bytes(bits_per_coefficient: usize, serialized: &[u8]) -> Self {
        let bit_vector = helpers::bytes_to_bit_vector(serialized);
        let mut bit_vector_chunks = bit_vector.chunks(bits_per_coefficient);

        let mut deserialized = KyberPolynomialRingElement::ZERO;

        for i in 0..deserialized.coefficients.len() {
            deserialized.coefficients[i] = KyberFieldElement::new_from_bit_vector(bits_per_coefficient, bit_vector_chunks.next().unwrap());
        }

        deserialized
    }
}
