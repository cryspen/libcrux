use crate::ring::RingElement;
use crate::field::FieldElement;
use crate::bit_vector::*;
use crate::parameters;

pub(crate) fn encode(r : &RingElement) -> [u8; parameters::L * 32] {
    let bit_vector = ring_element_to_bits(&r);
    assert_eq!(bit_vector.len(), r.coefficients.len() * parameters::L);

    let mut out = [0u8; parameters::L * 32];

    for i in 0..out.len() {
        out[i] = bits_to_u8(&bit_vector[i*8..(i+1)*8]);
    }
    out
}
//generate_array<const LEN: usize>(&[u8]) -> Result<[u8; LEN], Error>
#[allow(dead_code)]
pub(crate) fn decode(bytes : [u8; parameters::L * 32]) -> RingElement {
    let bit_vector = bytes_to_bits(&bytes[..]);
    assert_eq!(bit_vector.len(), parameters::L * 32 * (u8::BITS as usize));

    let mut out : RingElement = RingElement::ZERO;

    for i in 0..out.coefficients.len() {
        let coefficient = bits_to_u16(&bit_vector[i*parameters::L..(i + 1)*parameters::L]);
        out.coefficients[i] = FieldElement::from_u16(coefficient);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    extern crate getrandom;
    use getrandom::getrandom;

    #[test]
    fn apply_encode_then_decode() {
        let mut randombytes : [u8; 2] = [0; 2];

        let mut r = RingElement::ZERO;
        for i in 0..r.coefficients.len() {
            getrandom(&mut randombytes[..]).unwrap();
            let random_element = ((randombytes[1] as u16) << 8) | randombytes[0] as u16;
            r.coefficients[i] = FieldElement::from_u16(random_element);
        }

        let r_actual = decode(encode(&r));

        for i in 0..r.coefficients.len() {
            assert_eq!(r.coefficients[i].value, r_actual.coefficients[i].value);
        }
    }

}
