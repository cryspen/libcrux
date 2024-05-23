use crate::{
    arithmetic::PolynomialRingElement,
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS},
    hash_functions::XOF,
};

fn sample_from_uniform_distribution_next(
    randomness: &[u8],
    out: &mut PolynomialRingElement,
) -> usize {
    let mut sampled = 0;

    for bytes in randomness.chunks(3) {
        let b0 = bytes[0] as i32;
        let b1 = bytes[1] as i32;
        let b2 = bytes[2] as i32;

        let potential_coefficient = ((b2 << 16) | (b1 << 8) | b0) & 0x00_7F_FF_FF;

        if potential_coefficient < FIELD_MODULUS && sampled < COEFFICIENTS_IN_RING_ELEMENT {
            out.coefficients[sampled] = potential_coefficient;
            sampled += 1;
        }
    }

    sampled
}

pub(super) fn sample_ring_element_uniformly(seed: [u8; 34]) -> PolynomialRingElement {
    let mut state = XOF::new(seed);
    let randomness = XOF::squeeze_first_five_blocks(&mut state);

    let mut out = PolynomialRingElement::ZERO;

    let mut sampled = sample_from_uniform_distribution_next(&randomness, &mut out);

    while !(sampled >= COEFFICIENTS_IN_RING_ELEMENT) {
        let randomness = XOF::squeeze_next_block(&mut state);
        sampled += sample_from_uniform_distribution_next(&randomness, &mut out);
    }

    out
}
