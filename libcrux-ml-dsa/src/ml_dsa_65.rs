use crate::constants::*;

// ML-DSA-65 parameters

const ROWS_IN_A: usize = 6;
const COLUMNS_IN_A: usize = 5;

const ETA: usize = 4;
const TWO_TIMES_ETA_BIT_SIZE: usize = 4; // ⌊log_2(4)⌋ + 1

const VERIFICATION_KEY_SIZE: usize = SEED_FOR_A_SIZE
    + (COEFFICIENTS_IN_RING_ELEMENT
        * ROWS_IN_A
        * (FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - BITS_IN_LOWER_PART_OF_T))
        / 8;

const SIGNING_KEY_SIZE: usize = (SEED_FOR_A_SIZE + SEED_FOR_SIGNING_SIZE + HASH_OF_PUBLIC_KEY_SIZE)
    + (COEFFICIENTS_IN_RING_ELEMENT
        * (((ROWS_IN_A + COLUMNS_IN_A) * TWO_TIMES_ETA_BIT_SIZE)
            + (BITS_IN_LOWER_PART_OF_T * ROWS_IN_A)))
        / 8;

pub struct MLDSA65KeyPair {
    pub signing_key: [u8; SIGNING_KEY_SIZE],
    pub verification_key: [u8; VERIFICATION_KEY_SIZE],
}

/// Generate an ML-DSA-65 Key Pair
pub fn generate_key_pair(randomness: [u8; 32]) -> MLDSA65KeyPair {
    let (signing_key, verification_key) = crate::ml_dsa_generic::generate_key_pair::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        SIGNING_KEY_SIZE,
        VERIFICATION_KEY_SIZE,
    >(randomness);

    MLDSA65KeyPair {
        signing_key,
        verification_key,
    }
}
