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

const ERROR_RING_ELEMENT_SIZE: usize =
    (BITS_PER_ERROR_COEFFICIENT * COEFFICIENTS_IN_RING_ELEMENT) / 8;

// To sample a value in the interval [-(GAMMA - 1), GAMMA], we can sample a
// value (say 'v') in the interval [0, (2 * GAMMA) - 1] and then compute
// GAMMA - v. This can be done in 20 bits when GAMMA is 2^{19}.
const BITS_PER_MASK_COEFFICIENT: usize = 20;

const MAX_NUMBER_OF_ONES_IN_HINT: usize = 55;

const NUMBER_OF_ONES_IN_VERIFIER_CHALLENGE: usize = 49;

const ALPHA: i32 = 2 * ((FIELD_MODULUS - 1) / 32);

const BITS_PER_COMMITMENT_COEFFICIENT: usize =
    ((FIELD_MODULUS as usize) - 1) / ((ALPHA as usize) - 1);
const COMMITMENT_RING_ELEMENT_SIZE: usize =
    (BITS_PER_COMMITMENT_COEFFICIENT * COEFFICIENTS_IN_RING_ELEMENT) / 8;
const COMMITMENT_VECTOR_SIZE: usize = COMMITMENT_RING_ELEMENT_SIZE * ROWS_IN_A;

const MASK_RING_ELEMENT_SIZE: usize =
    (BITS_PER_MASK_COEFFICIENT * COEFFICIENTS_IN_RING_ELEMENT) / 8;

const COMMITMENT_HASH_SIZE: usize = 96;

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

const SIGNATURE_SIZE: usize = 1000;

pub struct MLDSA65SigningKey(pub [u8; SIGNING_KEY_SIZE]);
pub struct MLDSA65VerificationKey(pub [u8; VERIFICATION_KEY_SIZE]);

pub struct MLDSA65KeyPair {
    pub signing_key: MLDSA65SigningKey,
    pub verification_key: MLDSA65VerificationKey,
}

pub struct MLDSA65Signature(pub [u8; SIGNATURE_SIZE]);

/// Generate an ML-DSA-65 Key Pair
pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE]) -> MLDSA65KeyPair {
    let (signing_key, verification_key) = crate::ml_dsa_generic::generate_key_pair::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
        SIGNING_KEY_SIZE,
        VERIFICATION_KEY_SIZE,
    >(randomness);

    MLDSA65KeyPair {
        signing_key: MLDSA65SigningKey(signing_key),
        verification_key: MLDSA65VerificationKey(verification_key),
    }
}

/// Generate an ML-DSA-65 Signature
pub fn sign(
    signing_key: MLDSA65SigningKey,
    message: &[u8],
    randomness: [u8; SIGNING_RANDOMNESS_SIZE],
) -> MLDSA65Signature {
    let signature = crate::ml_dsa_generic::sign::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
        GAMMA1_EXPONENT,
        ALPHA,
        COMMITMENT_RING_ELEMENT_SIZE,
        COMMITMENT_VECTOR_SIZE,
        COMMITMENT_HASH_SIZE,
        NUMBER_OF_ONES_IN_VERIFIER_CHALLENGE,
        SIGNING_KEY_SIZE,
        SIGNATURE_SIZE,
    >(signing_key.0, message, randomness);

    MLDSA65Signature(signature)
}
