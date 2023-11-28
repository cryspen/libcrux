use super::{
    arithmetic::{FieldElement, PolynomialRingElement},
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS},
    Error,
};

// hax workaround to avoid local mutability.
#[inline(always)]
fn increment(x: &mut usize) {
    *x += 1;
}

pub fn sample_from_uniform_distribution<const SEED_SIZE: usize>(
    randomness: [u8; SEED_SIZE],
    sampling_error: &mut Option<Error>,
) -> PolynomialRingElement {
    let mut sampled_coefficients = 0;
    let mut out: PolynomialRingElement = PolynomialRingElement::ZERO;

    // This loop is written the way it is since reasoning about early returns,
    // breaks, and continues is not well supported in Fstar at the moment. Rewriting
    // this code to use an early return is being tracked in:
    // https://github.com/cryspen/libcrux/issues/134
    let mut done = [false];
    // for bytes in randomness.chunks(3) {
    for i in 0..randomness.len() / 3 {
    	let offset = i * 3;
        if !done[0] {
            let b1 = randomness[offset+0] as i32;
            let b2 = randomness[offset+1] as i32;
            let b3 = randomness[offset+2] as i32;

            let d1 = ((b2 & 0xF) << 8) | b1;
            let d2 = (b3 << 4) | (b2 >> 4);

            if d1 < FIELD_MODULUS && sampled_coefficients < COEFFICIENTS_IN_RING_ELEMENT {
                out.coefficients[sampled_coefficients] = d1;
                increment(&mut sampled_coefficients);
            }
            if d2 < FIELD_MODULUS && sampled_coefficients < COEFFICIENTS_IN_RING_ELEMENT {
                out.coefficients[sampled_coefficients] = d2;
                increment(&mut sampled_coefficients);
            }
            if sampled_coefficients == COEFFICIENTS_IN_RING_ELEMENT {
                done[0] = true;
            }
        }
    }
    if done[0] {
        hax_lib::debug_assert!(out
            .coefficients
            .into_iter()
            .all(|coefficient| coefficient >= 0 && coefficient < FIELD_MODULUS));
        *sampling_error = None;
        out
    } else {
        *sampling_error = Some(Error::RejectionSampling);
        out
    }
}

fn sample_from_binomial_distribution_2(randomness: &[u8]) -> PolynomialRingElement {
    let mut sampled: PolynomialRingElement = PolynomialRingElement::ZERO;

    // for (chunk_number, byte_chunk) in randomness.chunks_exact(4).enumerate() {
    for chunk_number in 0..randomness.len() / 4 {
    	let offset = chunk_number * 4;
        let random_bits_as_u32: u32 =
	      (randomness[offset+0] as u32)
            | (randomness[offset+1] as u32) << 8
            | (randomness[offset+2] as u32) << 16
            | (randomness[offset+3] as u32) << 24;

        let even_bits = random_bits_as_u32 & 0x55555555;
        let odd_bits = (random_bits_as_u32 >> 1) & 0x55555555;

        let coin_toss_outcomes = even_bits + odd_bits;

        // for outcome_set in (0..u32::BITS).step_by(4) {
        for i in 0..u32::BITS / 4 {
            let outcome_set = i * 4;
            let outcome_1 = ((coin_toss_outcomes >> outcome_set) & 0x3) as FieldElement;
            let outcome_2 = ((coin_toss_outcomes >> (outcome_set + 2)) & 0x3) as FieldElement;

            let offset = (outcome_set >> 2) as usize;
            sampled.coefficients[8 * chunk_number + offset] = outcome_1 - outcome_2;
        }
    }

    hax_lib::debug_assert!(sampled
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient >= -2 && coefficient <= 2));
    sampled
}

fn sample_from_binomial_distribution_3(randomness: &[u8]) -> PolynomialRingElement {
    let mut sampled: PolynomialRingElement = PolynomialRingElement::ZERO;

    // for (chunk_number, byte_chunk) in randomness.chunks_exact(3).enumerate() {
    for chunk_number in 0..randomness.len() / 3 {
	let offset = chunk_numer * 3;
        let random_bits_as_u24: u32 =
            (randomness[offset+0] as u32) | (randomness[offset+1] as u32) << 8 | (randomness[offset+2] as u32) << 16;

        let first_bits = random_bits_as_u24 & 0x00249249;
        let second_bits = (random_bits_as_u24 >> 1) & 0x00249249;
        let third_bits = (random_bits_as_u24 >> 2) & 0x00249249;

        let coin_toss_outcomes = first_bits + second_bits + third_bits;

        // for outcome_set in (0..24).step_by(6) {
        for i in 0..24 / 6 {
            let outcome_set = i * 6;
            let outcome_1 = ((coin_toss_outcomes >> outcome_set) & 0x7) as FieldElement;
            let outcome_2 = ((coin_toss_outcomes >> (outcome_set + 3)) & 0x7) as FieldElement;

            let offset = (outcome_set / 6) as usize;
            sampled.coefficients[4 * chunk_number + offset] = outcome_1 - outcome_2;
        }
    }

    hax_lib::debug_assert!(sampled
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient >= -3 && coefficient <= 3));
    sampled
}

#[inline(always)]
pub(super) fn sample_from_binomial_distribution<const ETA: usize>(
    randomness: &[u8],
) -> PolynomialRingElement {
    hax_lib::debug_assert!(randomness.len() == ETA * 64);

    match ETA as u32 {
        2 => sample_from_binomial_distribution_2(randomness),
        3 => sample_from_binomial_distribution_3(randomness),
        _ => unreachable!(),
    }
}
