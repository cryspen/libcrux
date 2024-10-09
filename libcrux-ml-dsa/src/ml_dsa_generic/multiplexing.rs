use super::*;
use libcrux_platform;

// For the case where we didn't compile with the simd128/simd256 features but
// have a CPU that has it and thus tries to call the simd128/simd256 version,
// we fall back to the portable version in this case.

#[cfg(feature = "simd256")]
use instantiations::avx2::{
    generate_key_pair as generate_key_pair_avx2, sign as sign_avx2,
    sign_pre_hashed_shake128 as sign_pre_hashed_shake128_avx2, verify as verify_avx2,
    verify_pre_hashed_shake128 as verify_pre_hashed_shake128_avx2,
};

#[cfg(all(feature = "simd256", feature = "acvp"))]
use instantiations::avx2::{
    sign_internal as sign_internal_avx2, verify_internal as verify_internal_avx2,
};

#[cfg(feature = "simd128")]
use instantiations::neon::{
    generate_key_pair as generate_key_pair_neon, sign as sign_neon,
    sign_pre_hashed_shake128 as sign_pre_hashed_shake128_neon, verify as verify_neon,
    verify_pre_hashed_shake128 as verify_pre_hashed_shake128_neon,
};

#[cfg(all(feature = "simd128", feature = "acvp"))]
use instantiations::neon::{
    sign_internal as sign_internal_neon, verify_internal as verify_internal_neon,
};

#[cfg(not(feature = "simd256"))]
use instantiations::portable::{
    generate_key_pair as generate_key_pair_avx2, sign as sign_avx2,
    sign_pre_hashed_shake128 as sign_pre_hashed_shake128_avx2, verify as verify_avx2,
    verify_pre_hashed_shake128 as verify_pre_hashed_shake128_avx2,
};

#[cfg(all(not(feature = "simd256"), feature = "acvp"))]
use instantiations::portable::{
    sign_internal as sign_internal_avx2, verify_internal as verify_internal_avx2,
};

#[cfg(all(not(feature = "simd128"), feature = "acvp"))]
use instantiations::portable::{
    sign_internal as sign_internal_neon, verify_internal as verify_internal_neon,
};

#[cfg(not(feature = "simd128"))]
use instantiations::portable::{
    generate_key_pair as generate_key_pair_neon, sign as sign_neon,
    sign_pre_hashed_shake128 as sign_pre_hashed_shake128_neon, verify as verify_neon,
    verify_pre_hashed_shake128 as verify_pre_hashed_shake128_neon,
};

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
    if libcrux_platform::simd256_support() {
        generate_key_pair_avx2::<
            ROWS_IN_A,
            COLUMNS_IN_A,
            ETA,
            ERROR_RING_ELEMENT_SIZE,
            SIGNING_KEY_SIZE,
            VERIFICATION_KEY_SIZE,
        >(randomness)
    } else if libcrux_platform::simd128_support() {
        generate_key_pair_neon::<
            ROWS_IN_A,
            COLUMNS_IN_A,
            ETA,
            ERROR_RING_ELEMENT_SIZE,
            SIGNING_KEY_SIZE,
            VERIFICATION_KEY_SIZE,
        >(randomness)
    } else {
        instantiations::portable::generate_key_pair::<
            ROWS_IN_A,
            COLUMNS_IN_A,
            ETA,
            ERROR_RING_ELEMENT_SIZE,
            SIGNING_KEY_SIZE,
            VERIFICATION_KEY_SIZE,
        >(randomness)
    }
}

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
    if libcrux_platform::simd256_support() {
        sign_internal_avx2::<
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
        >(signing_key, message, randomness)
    } else if libcrux_platform::simd128_support() {
        sign_internal_neon::<
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
        >(signing_key, message, randomness)
    } else {
        instantiations::portable::sign_internal::<
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
        >(signing_key, message, randomness)
    }
}

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
    if libcrux_platform::simd256_support() {
        sign_avx2::<
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
        >(signing_key, message, context, randomness)
    } else if libcrux_platform::simd128_support() {
        sign_neon::<
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
        >(signing_key, message, context, randomness)
    } else {
        instantiations::portable::sign::<
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
        >(signing_key, message, context, randomness)
    }
}

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
    if libcrux_platform::simd256_support() {
        sign_pre_hashed_shake128_avx2::<
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
        >(signing_key, message, context, randomness)
    } else if libcrux_platform::simd128_support() {
        sign_pre_hashed_shake128_neon::<
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
        >(signing_key, message, context, randomness)
    } else {
        instantiations::portable::sign_pre_hashed_shake128::<
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
        >(signing_key, message, context, randomness)
    }
}

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
    verification_key_serialized: &[u8; VERIFICATION_KEY_SIZE],
    message: &[u8],
    signature_serialized: &[u8; SIGNATURE_SIZE],
) -> Result<(), VerificationError> {
    if libcrux_platform::simd256_support() {
        verify_internal_avx2::<
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
        >(verification_key_serialized, message, signature_serialized)
    } else if libcrux_platform::simd128_support() {
        verify_internal_neon::<
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
        >(verification_key_serialized, message, signature_serialized)
    } else {
        instantiations::portable::verify_internal::<
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
        >(verification_key_serialized, message, signature_serialized)
    }
}

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
    verification_key_serialized: &[u8; VERIFICATION_KEY_SIZE],
    message: &[u8],
    context: &[u8],
    signature_serialized: &[u8; SIGNATURE_SIZE],
) -> Result<(), VerificationError> {
    if libcrux_platform::simd256_support() {
        verify_avx2::<
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
        >(
            verification_key_serialized,
            message,
            context,
            signature_serialized,
        )
    } else if libcrux_platform::simd128_support() {
        verify_neon::<
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
        >(
            verification_key_serialized,
            message,
            context,
            signature_serialized,
        )
    } else {
        instantiations::portable::verify::<
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
        >(
            verification_key_serialized,
            message,
            context,
            signature_serialized,
        )
    }
}

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
    verification_key_serialized: &[u8; VERIFICATION_KEY_SIZE],
    message: &[u8],
    context: &[u8],
    signature_serialized: &[u8; SIGNATURE_SIZE],
) -> Result<(), VerificationError> {
    if libcrux_platform::simd256_support() {
        verify_pre_hashed_shake128_avx2::<
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
        >(
            verification_key_serialized,
            message,
            context,
            signature_serialized,
        )
    } else if libcrux_platform::simd128_support() {
        verify_pre_hashed_shake128_neon::<
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
        >(
            verification_key_serialized,
            message,
            context,
            signature_serialized,
        )
    } else {
        instantiations::portable::verify_pre_hashed_shake128::<
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
        >(
            verification_key_serialized,
            message,
            context,
            signature_serialized,
        )
    }
}
