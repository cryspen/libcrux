use crate::constants::*;

// ML-DSA-65 parameters

const ROWS_IN_A: usize = 6;
const COLUMNS_IN_A: usize = 5;

const ETA: usize = 4;
const GAMMA1_EXPONENT: usize = 19;

// To sample a value in the interval [-ETA, ETA], we can sample a value (say 'v')
// in the interval [0, 2 * ETA] and then compute ETA - v. This can be done in
// 4 bits when ETA is 4.
const BITS_PER_ERROR_COEFFICIENT: usize = 4;

const BYTES_FOR_ERROR_RING_ELEMENT: usize =
    (BITS_PER_ERROR_COEFFICIENT * COEFFICIENTS_IN_RING_ELEMENT) / 8;

// To sample a value in the interval [-(GAMMA - 1), GAMMA], we can sample a
// value (say 'v') in the interval [0, (2 * GAMMA) - 1] and then compute
// GAMMA - v. This can be done in 20 bits when GAMMA is 2^{19}.
const BITS_PER_MASK_COEFFICIENT: usize = 20;

const MAX_NUMBER_OF_ONES_IN_HINT: usize = 55;

const BYTES_PER_MASK_RING_ELEMENT: usize =
    (BITS_PER_MASK_COEFFICIENT * COEFFICIENTS_IN_RING_ELEMENT) / 8;

const VERIFICATION_KEY_SIZE: usize = SEED_FOR_A_SIZE
    + (COEFFICIENTS_IN_RING_ELEMENT
        * ROWS_IN_A
        * (FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - BITS_IN_LOWER_PART_OF_T))
        / 8;

const SIGNING_KEY_SIZE: usize = SEED_FOR_A_SIZE
    + SEED_FOR_SIGNING_SIZE
    + BYTES_FOR_VERIFICATION_KEY_HASH
    + (ROWS_IN_A + COLUMNS_IN_A) * BYTES_FOR_ERROR_RING_ELEMENT
    + ROWS_IN_A * BYTES_FOR_RING_ELEMENT_OF_T0S;

pub struct MLDSA65KeyPair {
    pub signing_key: [u8; SIGNING_KEY_SIZE],
    pub verification_key: [u8; VERIFICATION_KEY_SIZE],
}

/// Generate an ML-DSA-65 Key Pair
pub fn generate_key_pair(randomness: [u8; 32]) -> MLDSA65KeyPair {
    let (signing_key, verification_key) = crate::ml_dsa_generic::generate_key_pair::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        ETA,
        BYTES_FOR_ERROR_RING_ELEMENT,
        SIGNING_KEY_SIZE,
        VERIFICATION_KEY_SIZE,
    >(randomness);

    MLDSA65KeyPair {
        signing_key,
        verification_key,
    }
}
