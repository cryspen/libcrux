use crate::ring::{FieldElement, RingElement};
use crate::bit_vector::bytes_to_bits;
use crate::parameters;

pub(crate) fn parse(random_bytes : [u8; parameters::REJECTION_SAMPLING_BYTES]) -> Result<RingElement, &'static str> {
    let mut j : usize = 0;
    let mut out : RingElement = RingElement::ZERO;

    for i in (0..random_bytes.len()).step_by(3) {
        let byte = u16::from(random_bytes[i]);
        let byte1 = u16::from(random_bytes[i + 1]);
        let byte2 = u16::from(random_bytes[i + 2]);

        let d1 = byte + (256 * (byte1 % 16));
        let d2 = (byte1 / 16) + (16 * byte2); // N.B.: Integer division is flooring in Rust.

        // N.B.: In an efficient implementation, we'd break when j == parameters::N
        if d1 < parameters::Q && j < parameters::N {
            out.coefficients[j] = FieldElement::from_u16(d1);
            j += 1
        }
        if d2 < parameters::Q && j < parameters::N { 
            out.coefficients[j] = FieldElement::from_u16(d2);
            j += 1;
        }
    }

    if j == out.coefficients.len() {
        Ok(out)
    } else {
        Err("Could not sample RingElement.")
    }
}

pub(crate) fn cbd(random_bytes : [u8; parameters::ETA * 64]) -> RingElement {
    let bit_vector = bytes_to_bits(&random_bytes[..]);
    assert_eq!(bit_vector.len(), parameters::ETA * 64 * usize::try_from(u8::BITS).unwrap());

    let mut out : RingElement = RingElement::ZERO;

    for i in 0..out.coefficients.len() {
        let mut a : u8 = 0;
        for j in 0..parameters::ETA {
            a += bit_vector[2 * i * parameters::ETA + j];
        }

        let mut b : u8 = 0;
        for j in 0..parameters::ETA {
            b += bit_vector[2 * i * parameters::ETA + parameters::ETA + j];
        }

        out.coefficients[i] = FieldElement::from_u8(a - b);
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use parameters::REJECTION_SAMPLING_BYTES;

    #[test]
    fn parse_all_zeros() {
        let sampled_ring_element = parse([0; REJECTION_SAMPLING_BYTES]).unwrap();

        for i in 0..sampled_ring_element.coefficients.len() {
            assert_eq!(sampled_ring_element.coefficients[i].value, 0);
        }
    }

    #[test]
    #[should_panic]
    fn parse_all_max() {
        let _ = parse([u8::MAX; REJECTION_SAMPLING_BYTES]).unwrap();
    }
}
