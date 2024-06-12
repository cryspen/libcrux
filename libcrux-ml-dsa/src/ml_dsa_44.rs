use crate::constants::*;

// ML-DSA-44 parameters

const ROWS_IN_A: usize = 4;
const COLUMNS_IN_A: usize = 4;

const ETA: usize = 2;
const BITS_PER_ERROR_COEFFICIENT: usize = 3;

const ERROR_RING_ELEMENT_SIZE: usize =
    (BITS_PER_ERROR_COEFFICIENT * COEFFICIENTS_IN_RING_ELEMENT) / 8;

const VERIFICATION_KEY_SIZE: usize = SEED_FOR_A_SIZE
    + (COEFFICIENTS_IN_RING_ELEMENT
        * ROWS_IN_A
        * (FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - BITS_IN_LOWER_PART_OF_T))
        / 8;

const SIGNING_KEY_SIZE: usize = SEED_FOR_A_SIZE
    + SEED_FOR_SIGNING_SIZE
    + BYTES_FOR_VERIFICATION_KEY_HASH
    + (ROWS_IN_A + COLUMNS_IN_A) * ERROR_RING_ELEMENT_SIZE
    + ROWS_IN_A * RING_ELEMENT_OF_T0S_SIZE;

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
        ERROR_RING_ELEMENT_SIZE,
        SIGNING_KEY_SIZE,
        VERIFICATION_KEY_SIZE,
    >(randomness);

    MLDSA65KeyPair {
        signing_key,
        verification_key,
    }
}
