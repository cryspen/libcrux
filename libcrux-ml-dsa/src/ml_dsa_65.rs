use crate::constants::*;

// ML-DSA-65 parameters

const ROWS_IN_A: usize = 6;
const COLUMNS_IN_A: usize = 5;

const PUBLIC_KEY_SIZE: usize =
    32 + (32 * ROWS_IN_A * (FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - DROPPED_BITS_FROM_T));
const SECRET_KEY_SIZE: usize =
    (32 + 32 + 64) + 32 * (((ROWS_IN_A + COLUMNS_IN_A) * 4) + (DROPPED_BITS_FROM_T * ROWS_IN_A));

pub struct MLDSA65KeyPair {
    pub secret_key: [u8; SECRET_KEY_SIZE],
    pub public_key: [u8; PUBLIC_KEY_SIZE],
}

/// Generate an ML-DSA-65 Key Pair
pub fn generate_key_pair(randomness: [u8; 32]) -> MLDSA65KeyPair {
    let (secret_key, public_key) =
        crate::ml_dsa_generic::generate_key_pair::<SECRET_KEY_SIZE, PUBLIC_KEY_SIZE>(randomness);

    MLDSA65KeyPair {
        secret_key,
        public_key,
    }
}
