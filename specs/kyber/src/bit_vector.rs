use crate::parameters;
use crate::ring::RingElement;

//TODO: look into using generate_array<const LEN: usize>(&[u8]) -> Result<[u8; LEN], Error>

pub(crate) fn bytes_to_bits(bytes : &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(bytes.len() * usize::try_from(u8::BITS).unwrap());

    for byte in bytes {
        for j in 0..u8::BITS {
            out.push((byte >> j) & 1);
        }
    }
    out
}

pub(crate) fn ring_element_to_bits(r : &RingElement) -> Vec<u8> {
    let mut out = Vec::with_capacity(r.coefficients.len() * parameters::BITS_PER_COEFFICIENT);

    for coeff in &r.coefficients {
        for j in 0..parameters::BITS_PER_COEFFICIENT {
            out.push(((coeff.value >> j) & 1).try_into().unwrap());
        }
    }
    out
}

#[allow(dead_code)]
pub(crate) fn bits_to_u16(bit_vector : &[u8]) -> u16 {
    assert_eq!(bit_vector.len(), parameters::BITS_PER_COEFFICIENT);
    let mut result : u16 = 0;
    for i in 0..parameters::BITS_PER_COEFFICIENT {
        result += u16::from(bit_vector[i]) * 2u16.pow(i.try_into().unwrap());
    }
    result
}

pub(crate) fn bits_to_u8(bit_vector : &[u8]) -> u8 {
    assert_eq!(bit_vector.len(), usize::try_from(u8::BITS).unwrap());
    let mut result : u8 = 0;
    for i in 0..8 {
        result += bit_vector[i] * 2u8.pow(i.try_into().unwrap());
    }
    result
}
