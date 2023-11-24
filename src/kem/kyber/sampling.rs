use super::{
    arithmetic::{KyberFieldElement, KyberPolynomialRingElement},
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS},
    Error,
};

pub fn sample_from_uniform_distribution<const SEED_SIZE: usize>(
    randomness: [u8; SEED_SIZE],
) -> (KyberPolynomialRingElement, Option<Error>) {
    let mut sampled_coefficients: [usize; 1] = [0];
    let mut out: KyberPolynomialRingElement = KyberPolynomialRingElement::ZERO;
    let mut done: [bool; 1] = [false];

    let max: usize = randomness.len() / 3;
    for i in 0..max {
        if !done[0] {
            let b1 = randomness[i * 3 + 0] as i32;
            let b2 = randomness[i * 3 + 1] as i32;
            let b3 = randomness[i * 3 + 2] as i32;

            let d1 = ((b2 & 0xF) << 8) | b1;
            let d2 = (b3 << 4) | (b2 >> 4);

            if d1 < FIELD_MODULUS && sampled_coefficients[0] < COEFFICIENTS_IN_RING_ELEMENT {
                out.coefficients[sampled_coefficients[0]] = d1;
                sampled_coefficients[0] += 1
            }
            if d2 < FIELD_MODULUS && sampled_coefficients[0] < COEFFICIENTS_IN_RING_ELEMENT {
                out.coefficients[sampled_coefficients[0]] = d2;
                sampled_coefficients[0] += 1;
            }
            if sampled_coefficients[0] == COEFFICIENTS_IN_RING_ELEMENT {
                done[0] = true;
            }
        }
    }
    if done[0] {
        // hax_lib::debug_assert!(out
        //     .coefficients
        //     .into_iter()
        //     .all(|coefficient| coefficient >= 0 && coefficient < FIELD_MODULUS));
        (out, None)
    } else {
        (out, Some(Error::RejectionSampling))
    }
}

fn sample_from_binomial_distribution_2(randomness: &[u8]) -> KyberPolynomialRingElement {
    let mut sampled: KyberPolynomialRingElement = KyberPolynomialRingElement::ZERO;

    for chunk_number in 0..(randomness.len() / 4) {
        // for (chunk_number, byte_chunk) in randomness.chunks_exact(4).enumerate() {
        let random_bits_as_u32: u32 = (randomness[chunk_number * 4 + 0] as u32)
            | (randomness[chunk_number * 4 + 1] as u32) << 8
            | (randomness[chunk_number * 4 + 2] as u32) << 16
            | (randomness[chunk_number * 4 + 3] as u32) << 24;

        let even_bits = random_bits_as_u32 & 0x55555555;
        let odd_bits = (random_bits_as_u32 >> 1) & 0x55555555;

        let coin_toss_outcomes = even_bits + odd_bits;

        for i in 0..(u32::BITS / 4) {
            let outcome_set = i * 4;
            let outcome_1 = ((coin_toss_outcomes >> outcome_set) & 0x3) as KyberFieldElement;
            let outcome_2 = ((coin_toss_outcomes >> (outcome_set + 2)) & 0x3) as KyberFieldElement;

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

fn sample_from_binomial_distribution_3(randomness: &[u8]) -> KyberPolynomialRingElement {
    let mut sampled: KyberPolynomialRingElement = KyberPolynomialRingElement::ZERO;

    for chunk_number in 0..(randomness.len() / 3) {
        // for (chunk_number, byte_chunk) in randomness.chunks_exact(3).enumerate() {
        let random_bits_as_u24: u32 = (randomness[chunk_number * 3 + 0] as u32)
            | (randomness[chunk_number * 3 + 1] as u32) << 8
            | (randomness[chunk_number * 3 + 2] as u32) << 16;

        let first_bits = random_bits_as_u24 & 0x00249249;
        let second_bits = (random_bits_as_u24 >> 1) & 0x00249249;
        let third_bits = (random_bits_as_u24 >> 2) & 0x00249249;

        let coin_toss_outcomes = first_bits + second_bits + third_bits;

        // for outcome_set in (0..24).step_by(6) {
        for i in 0..(24 / 6) {
            let outcome_set = i * 6;
            let outcome_1 = ((coin_toss_outcomes >> outcome_set) & 0x7) as KyberFieldElement;
            let outcome_2 = ((coin_toss_outcomes >> (outcome_set + 3)) & 0x7) as KyberFieldElement;

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
) -> KyberPolynomialRingElement {
    hax_lib::debug_assert!(randomness.len() == ETA * 64);

    match ETA as u32 {
        2 => sample_from_binomial_distribution_2(randomness),
        3 => sample_from_binomial_distribution_3(randomness),
        _ => unreachable!(),
    }
}
