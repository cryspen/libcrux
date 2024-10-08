use crate::{
    constants::*,
    ml_dsa_generic::{self, multiplexing},
    types::*,
    SigningError, VerificationError,
};

// ML-DSA-87 parameters

// TODO:
// - factor out the math for the constants across the three variants.

const ROWS_IN_A: usize = 8;
const COLUMNS_IN_A: usize = 7;

const ETA: usize = 2;

// To sample a value in the interval [-ETA, ETA], we can sample a value (say 'v')
// in the interval [0, 2 * ETA] and then compute ETA - v. This can be done in
// 3 bits when ETA is 2.
const BITS_PER_ERROR_COEFFICIENT: usize = 3;

const ERROR_RING_ELEMENT_SIZE: usize =
    (BITS_PER_ERROR_COEFFICIENT * COEFFICIENTS_IN_RING_ELEMENT) / 8;

const GAMMA1_EXPONENT: usize = 19;
// To sample a value in the interval [-(GAMMA - 1), GAMMA], we can sample a
// value (say 'v') in the interval [0, (2 * GAMMA) - 1] and then compute
// GAMMA - v. This can be done in 20 bits when GAMMA is 2^{19}.
const BITS_PER_GAMMA1_COEFFICIENT: usize = 20;
const GAMMA1_RING_ELEMENT_SIZE: usize =
    (BITS_PER_GAMMA1_COEFFICIENT * COEFFICIENTS_IN_RING_ELEMENT) / 8;

const MAX_ONES_IN_HINT: usize = 75;

const ONES_IN_VERIFIER_CHALLENGE: usize = 60;

const GAMMA2: i32 = (FIELD_MODULUS - 1) / 32;

const BETA: i32 = (ONES_IN_VERIFIER_CHALLENGE * ETA) as i32;

// Commitment coefficients are in the interval: [0, ((FIELD_MODULUS − 1)/2γ2) − 1]
// ((FIELD_MODULUS − 1)/2γ2) − 1 = 15, which means we need 4 bits to represent a
// coefficient.
const BITS_PER_COMMITMENT_COEFFICIENT: usize = 4;

const COMMITMENT_RING_ELEMENT_SIZE: usize =
    (BITS_PER_COMMITMENT_COEFFICIENT * COEFFICIENTS_IN_RING_ELEMENT) / 8;
const COMMITMENT_VECTOR_SIZE: usize = COMMITMENT_RING_ELEMENT_SIZE * ROWS_IN_A;

const COMMITMENT_HASH_SIZE: usize = 64;

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

const SIGNATURE_SIZE: usize =
    COMMITMENT_HASH_SIZE + (COLUMNS_IN_A * GAMMA1_RING_ELEMENT_SIZE) + MAX_ONES_IN_HINT + ROWS_IN_A;

pub type MLDSA87SigningKey = MLDSASigningKey<SIGNING_KEY_SIZE>;
pub type MLDSA87VerificationKey = MLDSAVerificationKey<VERIFICATION_KEY_SIZE>;
pub type MLDSA87KeyPair = MLDSAKeyPair<VERIFICATION_KEY_SIZE, SIGNING_KEY_SIZE>;
pub type MLDSA87Signature = MLDSASignature<SIGNATURE_SIZE>;

// Instantiate the different functions.
macro_rules! instantiate {
    ($modp:ident, $p:path, $doc:expr) => {
        #[doc = $doc]
        pub mod $modp {
            use super::*;
            use $p as p;

            /// Generate an ML-DSA-87 Key Pair
            pub fn generate_key_pair(
                randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
            ) -> MLDSA87KeyPair {
                let (signing_key, verification_key) = p::generate_key_pair::<
                    ROWS_IN_A,
                    COLUMNS_IN_A,
                    ETA,
                    ERROR_RING_ELEMENT_SIZE,
                    SIGNING_KEY_SIZE,
                    VERIFICATION_KEY_SIZE,
                >(randomness);

                MLDSA87KeyPair {
                    signing_key: MLDSASigningKey(signing_key),
                    verification_key: MLDSAVerificationKey(verification_key),
                }
            }

            /// Generate an ML-DSA-87 Signature (Algorithm 7 in FIPS204)
            ///
            /// The message is assumed to be domain-separated.
            #[cfg(feature = "acvp")]
            pub fn sign_internal(
                signing_key: &MLDSA87SigningKey,
                message: &[u8],
                randomness: [u8; SIGNING_RANDOMNESS_SIZE],
            ) -> Result<MLDSA87Signature, SigningError> {
                p::sign_internal::<
                    ROWS_IN_A,
                    COLUMNS_IN_A,
                    ETA,
                    ERROR_RING_ELEMENT_SIZE,
                    GAMMA1_EXPONENT,
                    GAMMA2,
                    COMMITMENT_RING_ELEMENT_SIZE,
                    COMMITMENT_VECTOR_SIZE,
                    COMMITMENT_HASH_SIZE,
                    ONES_IN_VERIFIER_CHALLENGE,
                    MAX_ONES_IN_HINT,
                    GAMMA1_RING_ELEMENT_SIZE,
                    SIGNING_KEY_SIZE,
                    SIGNATURE_SIZE,
                >(&signing_key.0, message, randomness)
            }

            /// Verify an ML-DSA-87 Signature (Algorithm 8 in FIPS204)
            ///
            /// The message is assumed to be domain-separated.
            #[cfg(feature = "acvp")]
            pub fn verify_internal(
                verification_key: &MLDSA87VerificationKey,
                message: &[u8],
                signature: &MLDSA87Signature,
            ) -> Result<(), VerificationError> {
                p::verify_internal::<
                    ROWS_IN_A,
                    COLUMNS_IN_A,
                    SIGNATURE_SIZE,
                    VERIFICATION_KEY_SIZE,
                    GAMMA1_EXPONENT,
                    GAMMA1_RING_ELEMENT_SIZE,
                    GAMMA2,
                    BETA,
                    COMMITMENT_RING_ELEMENT_SIZE,
                    COMMITMENT_VECTOR_SIZE,
                    COMMITMENT_HASH_SIZE,
                    ONES_IN_VERIFIER_CHALLENGE,
                    MAX_ONES_IN_HINT,
                >(&verification_key.0, message, &signature.0)
            }

            /// Generate an ML-DSA-87 Signature
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn sign(
                signing_key: &MLDSA87SigningKey,
                message: &[u8],
                context: &[u8],
                randomness: [u8; SIGNING_RANDOMNESS_SIZE],
            ) -> Result<MLDSA87Signature, SigningError> {
                p::sign::<
                    ROWS_IN_A,
                    COLUMNS_IN_A,
                    ETA,
                    ERROR_RING_ELEMENT_SIZE,
                    GAMMA1_EXPONENT,
                    GAMMA2,
                    COMMITMENT_RING_ELEMENT_SIZE,
                    COMMITMENT_VECTOR_SIZE,
                    COMMITMENT_HASH_SIZE,
                    ONES_IN_VERIFIER_CHALLENGE,
                    MAX_ONES_IN_HINT,
                    GAMMA1_RING_ELEMENT_SIZE,
                    SIGNING_KEY_SIZE,
                    SIGNATURE_SIZE,
                >(&signing_key.0, message, context, randomness)
            }

            /// Generate a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn sign_pre_hashed_shake128(
                signing_key: &MLDSA87SigningKey,
                message: &[u8],
                context: &[u8],
                randomness: [u8; SIGNING_RANDOMNESS_SIZE],
            ) -> Result<MLDSA87Signature, SigningError> {
                p::sign_pre_hashed_shake128::<
                    ROWS_IN_A,
                    COLUMNS_IN_A,
                    ETA,
                    ERROR_RING_ELEMENT_SIZE,
                    GAMMA1_EXPONENT,
                    GAMMA2,
                    COMMITMENT_RING_ELEMENT_SIZE,
                    COMMITMENT_VECTOR_SIZE,
                    COMMITMENT_HASH_SIZE,
                    ONES_IN_VERIFIER_CHALLENGE,
                    MAX_ONES_IN_HINT,
                    GAMMA1_RING_ELEMENT_SIZE,
                    SIGNING_KEY_SIZE,
                    SIGNATURE_SIZE,
                >(&signing_key.0, message, context, randomness)
            }

            /// Verify an ML-DSA-87 Signature
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn verify(
                verification_key: &MLDSA87VerificationKey,
                message: &[u8],
                context: &[u8],
                signature: &MLDSA87Signature,
            ) -> Result<(), VerificationError> {
                p::verify::<
                    ROWS_IN_A,
                    COLUMNS_IN_A,
                    SIGNATURE_SIZE,
                    VERIFICATION_KEY_SIZE,
                    GAMMA1_EXPONENT,
                    GAMMA1_RING_ELEMENT_SIZE,
                    GAMMA2,
                    BETA,
                    COMMITMENT_RING_ELEMENT_SIZE,
                    COMMITMENT_VECTOR_SIZE,
                    COMMITMENT_HASH_SIZE,
                    ONES_IN_VERIFIER_CHALLENGE,
                    MAX_ONES_IN_HINT,
                >(&verification_key.0, message, context, &signature.0)
            }

            /// Verify a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn verify_pre_hashed_shake128(
                verification_key: &MLDSA87VerificationKey,
                message: &[u8],
                context: &[u8],
                signature: &MLDSA87Signature,
            ) -> Result<(), VerificationError> {
                p::verify_pre_hashed_shake128::<
                    ROWS_IN_A,
                    COLUMNS_IN_A,
                    SIGNATURE_SIZE,
                    VERIFICATION_KEY_SIZE,
                    GAMMA1_EXPONENT,
                    GAMMA1_RING_ELEMENT_SIZE,
                    GAMMA2,
                    BETA,
                    COMMITMENT_RING_ELEMENT_SIZE,
                    COMMITMENT_VECTOR_SIZE,
                    COMMITMENT_HASH_SIZE,
                    ONES_IN_VERIFIER_CHALLENGE,
                    MAX_ONES_IN_HINT,
                >(&verification_key.0, message, context, &signature.0)
            }
        }
    };
}

// Instantiations

instantiate! {portable, ml_dsa_generic::instantiations::portable, "Portable ML-DSA 87"}
#[cfg(feature = "simd256")]
instantiate! {avx2, ml_dsa_generic::instantiations::avx2, "AVX2 Optimised ML-DSA 87"}
#[cfg(feature = "simd128")]
instantiate! {neon, ml_dsa_generic::instantiations::neon, "Neon Optimised ML-DSA 87"}

/// Generate an ML-DSA 87 Key Pair
///
/// Generate an ML-DSA key pair. The input is a byte array of size
/// [`KEY_GENERATION_RANDOMNESS_SIZE`].
///
/// This function returns an [`MLDSA87KeyPair`].
#[cfg(not(eurydice))]
pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE]) -> MLDSA87KeyPair {
    let (signing_key, verification_key) = multiplexing::generate_key_pair::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
        SIGNING_KEY_SIZE,
        VERIFICATION_KEY_SIZE,
    >(randomness);

    MLDSA87KeyPair {
        signing_key: MLDSASigningKey(signing_key),
        verification_key: MLDSAVerificationKey(verification_key),
    }
}

/// Sign with ML-DSA 87
///
/// Sign a `message` with the ML-DSA `signing_key`.
///
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
///
/// This function returns an [`MLDSA87Signature`].
#[cfg(not(eurydice))]
pub fn sign(
    signing_key: &MLDSA87SigningKey,
    message: &[u8],
    context: &[u8],
    randomness: [u8; SIGNING_RANDOMNESS_SIZE],
) -> Result<MLDSA87Signature, SigningError> {
    multiplexing::sign::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
        GAMMA1_EXPONENT,
        GAMMA2,
        COMMITMENT_RING_ELEMENT_SIZE,
        COMMITMENT_VECTOR_SIZE,
        COMMITMENT_HASH_SIZE,
        ONES_IN_VERIFIER_CHALLENGE,
        MAX_ONES_IN_HINT,
        GAMMA1_RING_ELEMENT_SIZE,
        SIGNING_KEY_SIZE,
        SIGNATURE_SIZE,
    >(&signing_key.0, message, context, randomness)
}

/// Verify an ML-DSA-87 Signature
///
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
///
/// Returns `Ok` when the `signature` is valid for the `message` and
/// `verification_key`, and a [`VerificationError`] otherwise.
#[cfg(not(eurydice))]
pub fn verify(
    verification_key: &MLDSA87VerificationKey,
    message: &[u8],
    context: &[u8],
    signature: &MLDSA87Signature,
) -> Result<(), VerificationError> {
    multiplexing::verify::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        SIGNATURE_SIZE,
        VERIFICATION_KEY_SIZE,
        GAMMA1_EXPONENT,
        GAMMA1_RING_ELEMENT_SIZE,
        GAMMA2,
        BETA,
        COMMITMENT_RING_ELEMENT_SIZE,
        COMMITMENT_VECTOR_SIZE,
        COMMITMENT_HASH_SIZE,
        ONES_IN_VERIFIER_CHALLENGE,
        MAX_ONES_IN_HINT,
    >(&verification_key.0, message, context, &signature.0)
}

/// Sign with HashML-DSA 87, with a SHAKE128 pre-hashing
///
/// Sign a digest of `message` derived using `pre_hash` with the
/// ML-DSA `signing_key`.
///
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
///
/// This function returns an [`MLDSA87Signature`].
#[cfg(not(eurydice))]
pub fn sign_pre_hashed_shake128(
    signing_key: &MLDSA87SigningKey,
    message: &[u8],
    context: &[u8],
    randomness: [u8; SIGNING_RANDOMNESS_SIZE],
) -> Result<MLDSA87Signature, SigningError> {
    multiplexing::sign_pre_hashed_shake128::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
        GAMMA1_EXPONENT,
        GAMMA2,
        COMMITMENT_RING_ELEMENT_SIZE,
        COMMITMENT_VECTOR_SIZE,
        COMMITMENT_HASH_SIZE,
        ONES_IN_VERIFIER_CHALLENGE,
        MAX_ONES_IN_HINT,
        GAMMA1_RING_ELEMENT_SIZE,
        SIGNING_KEY_SIZE,
        SIGNATURE_SIZE,
    >(&signing_key.0, message, context, randomness)
}

/// Verify a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing
///
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
///
/// Returns `Ok` when the `signature` is valid for the `message` and
/// `verification_key`, and a [`VerificationError`] otherwise.
#[cfg(not(eurydice))]
pub fn verify_pre_hashed_shake128(
    verification_key: &MLDSA87VerificationKey,
    message: &[u8],
    context: &[u8],
    signature: &MLDSA87Signature,
) -> Result<(), VerificationError> {
    multiplexing::verify_pre_hashed_shake128::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        SIGNATURE_SIZE,
        VERIFICATION_KEY_SIZE,
        GAMMA1_EXPONENT,
        GAMMA1_RING_ELEMENT_SIZE,
        GAMMA2,
        BETA,
        COMMITMENT_RING_ELEMENT_SIZE,
        COMMITMENT_VECTOR_SIZE,
        COMMITMENT_HASH_SIZE,
        ONES_IN_VERIFIER_CHALLENGE,
        MAX_ONES_IN_HINT,
    >(&verification_key.0, message, context, &signature.0)
}

/// Sign with ML-DSA 87 (Algorithm 7 in FIPS204)
///
/// Sign a `message` (assumed to be domain-separated) with the ML-DSA `signing_key`.
///
/// This function returns an [`MLDSA87Signature`].
#[cfg(all(not(eurydice), feature = "acvp"))]
pub fn sign_internal(
    signing_key: &MLDSA87SigningKey,
    message: &[u8],
    randomness: [u8; SIGNING_RANDOMNESS_SIZE],
) -> Result<MLDSA87Signature, SigningError> {
    multiplexing::sign_internal::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
        GAMMA1_EXPONENT,
        GAMMA2,
        COMMITMENT_RING_ELEMENT_SIZE,
        COMMITMENT_VECTOR_SIZE,
        COMMITMENT_HASH_SIZE,
        ONES_IN_VERIFIER_CHALLENGE,
        MAX_ONES_IN_HINT,
        GAMMA1_RING_ELEMENT_SIZE,
        SIGNING_KEY_SIZE,
        SIGNATURE_SIZE,
    >(&signing_key.0, message, randomness)
}

/// Verify an ML-DSA-87 Signature (Algorithm 8 in FIPS204)
///
/// Returns `Ok` when the `signature` is valid for the `message` (assumed to be domain-separated) and
/// `verification_key`, and a [`VerificationError`] otherwise.
#[cfg(all(not(eurydice), feature = "acvp"))]
pub fn verify_internal(
    verification_key: &MLDSA87VerificationKey,
    message: &[u8],
    signature: &MLDSA87Signature,
) -> Result<(), VerificationError> {
    multiplexing::verify_internal::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        SIGNATURE_SIZE,
        VERIFICATION_KEY_SIZE,
        GAMMA1_EXPONENT,
        GAMMA1_RING_ELEMENT_SIZE,
        GAMMA2,
        BETA,
        COMMITMENT_RING_ELEMENT_SIZE,
        COMMITMENT_VECTOR_SIZE,
        COMMITMENT_HASH_SIZE,
        ONES_IN_VERIFIER_CHALLENGE,
        MAX_ONES_IN_HINT,
    >(&verification_key.0, message, &signature.0)
}
