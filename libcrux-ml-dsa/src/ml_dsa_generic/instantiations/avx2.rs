use crate::{
    constants::*,
    ml_dsa_generic::{SigningError, VerificationError},
    pre_hash::SHAKE128_PH,
    types::*,
};

mod avx2_feature {
    use super::*;

    /// Generate key pair.
    #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
    #[allow(unsafe_code)]
    pub(super) unsafe fn generate_key_pair_v44(
        randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
        signing_key: &mut [u8],
        verification_key: &mut [u8],
    ) {
        crate::ml_dsa_generic::generate_key_pair_v44::<
            crate::simd::avx2::AVX2SIMDUnit,
            crate::samplex4::avx2::AVX2Sampler,
            crate::hash_functions::simd256::Shake128x4,
            crate::hash_functions::simd256::Shake256,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake256Xof,
            crate::hash_functions::simd256::Shake256x4,
        >(randomness, signing_key, verification_key)
    }

    /// Generate key pair.
    #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
    #[allow(unsafe_code)]
    pub(super) unsafe fn generate_key_pair_v65(
        randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
        signing_key: &mut [u8],
        verification_key: &mut [u8],
    ) {
        crate::ml_dsa_generic::generate_key_pair_v65::<
            crate::simd::avx2::AVX2SIMDUnit,
            crate::samplex4::avx2::AVX2Sampler,
            crate::hash_functions::simd256::Shake128x4,
            crate::hash_functions::simd256::Shake256,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake256Xof,
            crate::hash_functions::simd256::Shake256x4,
        >(randomness, signing_key, verification_key)
    }

    /// Generate key pair.
    #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
    #[allow(unsafe_code)]
    pub(super) unsafe fn generate_key_pair_v87(
        randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
        signing_key: &mut [u8],
        verification_key: &mut [u8],
    ) {
        crate::ml_dsa_generic::generate_key_pair_v87::<
            crate::simd::avx2::AVX2SIMDUnit,
            crate::samplex4::avx2::AVX2Sampler,
            crate::hash_functions::simd256::Shake128x4,
            crate::hash_functions::simd256::Shake256,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake256Xof,
            crate::hash_functions::simd256::Shake256x4,
        >(randomness, signing_key, verification_key)
    }

    /// Sign.
    #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
    #[allow(unsafe_code)]
    pub(super) unsafe fn sign<
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
            crate::simd::avx2::AVX2SIMDUnit,
            crate::samplex4::avx2::AVX2Sampler,
            crate::hash_functions::simd256::Shake128x4,
            crate::hash_functions::simd256::Shake256,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake256Xof,
            crate::hash_functions::simd256::Shake256x4,
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
    #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
    #[allow(unsafe_code)]
    pub(super) unsafe fn sign_internal<
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
            crate::simd::avx2::AVX2SIMDUnit,
            crate::samplex4::avx2::AVX2Sampler,
            crate::hash_functions::simd256::Shake128x4,
            crate::hash_functions::simd256::Shake256,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake256Xof,
            crate::hash_functions::simd256::Shake256x4,
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
    #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
    #[allow(unsafe_code)]
    pub(super) unsafe fn sign_pre_hashed_shake128<
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
            crate::simd::avx2::AVX2SIMDUnit,
            crate::samplex4::avx2::AVX2Sampler,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake128,
            crate::hash_functions::simd256::Shake128x4,
            crate::hash_functions::simd256::Shake256,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake256Xof,
            crate::hash_functions::simd256::Shake256x4,
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
    #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
    #[allow(unsafe_code)]
    pub(super) unsafe fn verify<
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
            crate::simd::avx2::AVX2SIMDUnit,
            crate::samplex4::avx2::AVX2Sampler,
            crate::hash_functions::simd256::Shake128x4,
            crate::hash_functions::simd256::Shake256,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake256Xof,
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
    #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
    #[allow(unsafe_code)]
    pub(super) unsafe fn verify_internal<
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
            crate::simd::avx2::AVX2SIMDUnit,
            crate::samplex4::avx2::AVX2Sampler,
            crate::hash_functions::simd256::Shake128x4,
            crate::hash_functions::simd256::Shake256,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake256Xof,
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
    #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
    #[allow(unsafe_code)]
    pub(super) unsafe fn verify_pre_hashed_shake128<
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
            crate::simd::avx2::AVX2SIMDUnit,
            crate::samplex4::avx2::AVX2Sampler,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake128,
            crate::hash_functions::simd256::Shake128x4,
            crate::hash_functions::simd256::Shake256,
            // We use the portable version here.
            // It doesn' make sense to do these in parallel.
            crate::hash_functions::portable::Shake256Xof,
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

/// Generate key pair.
#[allow(unsafe_code)]
pub(crate) fn generate_key_pair_v44(
    randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
    signing_key: &mut [u8],
    verification_key: &mut [u8],
) {
    unsafe { avx2_feature::generate_key_pair_v44(randomness, signing_key, verification_key) }
}

/// Generate key pair.
#[allow(unsafe_code)]
pub(crate) fn generate_key_pair_v65(
    randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
    signing_key: &mut [u8],
    verification_key: &mut [u8],
) {
    unsafe { avx2_feature::generate_key_pair_v65(randomness, signing_key, verification_key) }
}

/// Generate key pair.
#[allow(unsafe_code)]
pub(crate) fn generate_key_pair_v87(
    randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
    signing_key: &mut [u8],
    verification_key: &mut [u8],
) {
    unsafe { avx2_feature::generate_key_pair_v87(randomness, signing_key, verification_key) }
}

/// Sign.
#[allow(unsafe_code)]
#[inline(always)]
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
    unsafe {
        avx2_feature::sign::<
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

/// Sign (internal API)
#[cfg(feature = "acvp")]
#[allow(unsafe_code)]
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
    unsafe {
        avx2_feature::sign_internal::<
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

/// Sign (pre-hashed).
#[allow(unsafe_code)]
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
    unsafe {
        avx2_feature::sign_pre_hashed_shake128::<
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

/// Verify.
#[allow(unsafe_code)]
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
    unsafe {
        avx2_feature::verify::<
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

/// Verify (internal API).
#[cfg(feature = "acvp")]
#[allow(unsafe_code)]
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
    unsafe {
        avx2_feature::verify_internal::<
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
        >(verification_key, message, signature)
    }
}

/// Verify (pre-hashed with SHAKE-128).
#[allow(unsafe_code)]
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
    unsafe {
        avx2_feature::verify_pre_hashed_shake128::<
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
