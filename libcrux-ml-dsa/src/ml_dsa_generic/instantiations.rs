macro_rules! instantiate {
    ($modp:ident, $simdunit:path, $shake128x4:path, $shake256:path, $shake256x4:path) => {
        pub mod $modp {
            use crate::{
                constants::*,
                ml_dsa_generic::{SigningError, VerificationError},
                pre_hash::SHAKE128_PH,
                types::*,
            };

            /// Generate key pair.
            pub(crate) fn generate_key_pair<
                const ROWS_IN_A: usize,
                const COLUMNS_IN_A: usize,
                const ETA: usize,
                const ERROR_RING_ELEMENT_SIZE: usize,
                const SIGNING_KEY_SIZE: usize,
                const VERIFICATION_KEY_SIZE: usize,
            >(
                randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
            ) -> ([u8; SIGNING_KEY_SIZE], [u8; VERIFICATION_KEY_SIZE]) {
                crate::ml_dsa_generic::generate_key_pair::<
                    $simdunit,
                    $shake128x4,
                    $shake256,
                    $shake256x4,
                    ROWS_IN_A,
                    COLUMNS_IN_A,
                    ETA,
                    ERROR_RING_ELEMENT_SIZE,
                    SIGNING_KEY_SIZE,
                    VERIFICATION_KEY_SIZE,
                >(randomness)
            }

            /// Sign.
            pub(crate) fn sign<
                const ROWS_IN_A: usize,
                const COLUMNS_IN_A: usize,
                const ETA: usize,
                const ERROR_RING_ELEMENT_SIZE: usize,
                const GAMMA1_EXPONENT: usize,
                const GAMMA2: i32,
                const COMMITMENT_RING_ELEMENT_SIZE: usize,
                const COMMITMENT_VECTOR_SIZE: usize,
                const COMMITMENT_HASH_SIZE: usize,
                const ONES_IN_VERIFIER_CHALLENGE: usize,
                const MAX_ONES_IN_HINT: usize,
                const GAMMA1_RING_ELEMENT_SIZE: usize,
                const SIGNING_KEY_SIZE: usize,
                const SIGNATURE_SIZE: usize,
            >(
                signing_key: &[u8; SIGNING_KEY_SIZE],
                message: &[u8],
                context: &[u8],
                randomness: [u8; SIGNING_RANDOMNESS_SIZE],
            ) -> Result<MLDSASignature<SIGNATURE_SIZE>, SigningError> {
                crate::ml_dsa_generic::sign::<
                    $simdunit,
                    $shake128x4,
                    $shake256,
                    $shake256x4,
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
                >(&signing_key, message, context, randomness)
            }

            /// Sign (internal API)
            #[cfg(feature = "acvp")]
            pub(crate) fn sign_internal<
                const ROWS_IN_A: usize,
                const COLUMNS_IN_A: usize,
                const ETA: usize,
                const ERROR_RING_ELEMENT_SIZE: usize,
                const GAMMA1_EXPONENT: usize,
                const GAMMA2: i32,
                const COMMITMENT_RING_ELEMENT_SIZE: usize,
                const COMMITMENT_VECTOR_SIZE: usize,
                const COMMITMENT_HASH_SIZE: usize,
                const ONES_IN_VERIFIER_CHALLENGE: usize,
                const MAX_ONES_IN_HINT: usize,
                const GAMMA1_RING_ELEMENT_SIZE: usize,
                const SIGNING_KEY_SIZE: usize,
                const SIGNATURE_SIZE: usize,
            >(
                signing_key: &[u8; SIGNING_KEY_SIZE],
                message: &[u8],
                randomness: [u8; SIGNING_RANDOMNESS_SIZE],
            ) -> Result<MLDSASignature<SIGNATURE_SIZE>, SigningError> {
                crate::ml_dsa_generic::sign_internal::<
                    $simdunit,
                    $shake128x4,
                    $shake256,
                    $shake256x4,
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
                >(&signing_key, message, None, randomness)
            }

            /// Sign (pre-hashed).
            pub(crate) fn sign_pre_hashed_shake128<
                const ROWS_IN_A: usize,
                const COLUMNS_IN_A: usize,
                const ETA: usize,
                const ERROR_RING_ELEMENT_SIZE: usize,
                const GAMMA1_EXPONENT: usize,
                const GAMMA2: i32,
                const COMMITMENT_RING_ELEMENT_SIZE: usize,
                const COMMITMENT_VECTOR_SIZE: usize,
                const COMMITMENT_HASH_SIZE: usize,
                const ONES_IN_VERIFIER_CHALLENGE: usize,
                const MAX_ONES_IN_HINT: usize,
                const GAMMA1_RING_ELEMENT_SIZE: usize,
                const SIGNING_KEY_SIZE: usize,
                const SIGNATURE_SIZE: usize,
            >(
                signing_key: &[u8; SIGNING_KEY_SIZE],
                message: &[u8],
                context: &[u8],
                randomness: [u8; SIGNING_RANDOMNESS_SIZE],
            ) -> Result<MLDSASignature<SIGNATURE_SIZE>, SigningError> {
                crate::ml_dsa_generic::sign_pre_hashed::<
                    $simdunit,
                    $shake128x4,
                    $shake256,
                    $shake256x4,
                    SHAKE128_PH,
                    256,
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
                >(&signing_key, message, context, randomness)
            }

            /// Verify.
            pub(crate) fn verify<
                const ROWS_IN_A: usize,
                const COLUMNS_IN_A: usize,
                const SIGNATURE_SIZE: usize,
                const VERIFICATION_KEY_SIZE: usize,
                const GAMMA1_EXPONENT: usize,
                const GAMMA1_RING_ELEMENT_SIZE: usize,
                const GAMMA2: i32,
                const BETA: i32,
                const COMMITMENT_RING_ELEMENT_SIZE: usize,
                const COMMITMENT_VECTOR_SIZE: usize,
                const COMMITMENT_HASH_SIZE: usize,
                const ONES_IN_VERIFIER_CHALLENGE: usize,
                const MAX_ONES_IN_HINT: usize,
            >(
                verification_key: &[u8; VERIFICATION_KEY_SIZE],
                message: &[u8],
                context: &[u8],
                signature: &[u8; SIGNATURE_SIZE],
            ) -> Result<(), VerificationError> {
                crate::ml_dsa_generic::verify::<
                    $simdunit,
                    $shake128x4,
                    $shake256,
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
                >(verification_key, message, context, signature)
            }

            /// Verify (internal API).
            #[cfg(feature = "acvp")]
            pub(crate) fn verify_internal<
                const ROWS_IN_A: usize,
                const COLUMNS_IN_A: usize,
                const SIGNATURE_SIZE: usize,
                const VERIFICATION_KEY_SIZE: usize,
                const GAMMA1_EXPONENT: usize,
                const GAMMA1_RING_ELEMENT_SIZE: usize,
                const GAMMA2: i32,
                const BETA: i32,
                const COMMITMENT_RING_ELEMENT_SIZE: usize,
                const COMMITMENT_VECTOR_SIZE: usize,
                const COMMITMENT_HASH_SIZE: usize,
                const ONES_IN_VERIFIER_CHALLENGE: usize,
                const MAX_ONES_IN_HINT: usize,
            >(
                verification_key: &[u8; VERIFICATION_KEY_SIZE],
                message: &[u8],
                signature: &[u8; SIGNATURE_SIZE],
            ) -> Result<(), VerificationError> {
                crate::ml_dsa_generic::verify_internal::<
                    $simdunit,
                    $shake128x4,
                    $shake256,
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
                >(verification_key, message, None, signature)
            }

            /// Verify (pre-hashed with SHAKE-128).
            pub(crate) fn verify_pre_hashed_shake128<
                const ROWS_IN_A: usize,
                const COLUMNS_IN_A: usize,
                const SIGNATURE_SIZE: usize,
                const VERIFICATION_KEY_SIZE: usize,
                const GAMMA1_EXPONENT: usize,
                const GAMMA1_RING_ELEMENT_SIZE: usize,
                const GAMMA2: i32,
                const BETA: i32,
                const COMMITMENT_RING_ELEMENT_SIZE: usize,
                const COMMITMENT_VECTOR_SIZE: usize,
                const COMMITMENT_HASH_SIZE: usize,
                const ONES_IN_VERIFIER_CHALLENGE: usize,
                const MAX_ONES_IN_HINT: usize,
            >(
                verification_key: &[u8; VERIFICATION_KEY_SIZE],
                message: &[u8],
                context: &[u8],
                signature: &[u8; SIGNATURE_SIZE],
            ) -> Result<(), VerificationError> {
                crate::ml_dsa_generic::verify_pre_hashed::<
                    $simdunit,
                    $shake128x4,
                    $shake256,
                    SHAKE128_PH,
                    256,
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
                >(verification_key, message, context, signature)
            }
        }
    };
}

// Portable generic implementations.
instantiate! {portable,
    crate::simd::portable::PortableSIMDUnit,
    crate::hash_functions::portable::Shake128X4,
    crate::hash_functions::portable::Shake256,
    crate::hash_functions::portable::Shake256X4
}

// AVX2 generic implementation.
#[cfg(feature = "simd256")]
instantiate! {avx2,
    crate::simd::avx2::AVX2SIMDUnit,
    crate::hash_functions::simd256::Shake128x4,
    crate::hash_functions::simd256::Shake256,
    crate::hash_functions::simd256::Shake256x4
}

// NEON generic implementation.
#[cfg(feature = "simd128")]
instantiate! {neon,
    crate::simd::portable::PortableSIMDUnit,
    crate::hash_functions::neon::Shake128x4,
    crate::hash_functions::portable::Shake256,
    crate::hash_functions::neon::Shake256x4
}
