use libcrux_sha3::portable::incremental::{Shake256Absorb, XofAbsorb, XofSqueeze};

use crate::{
    arithmetic::{
        decompose_vector, make_hint, power2round_vector, use_hint, vector_infinity_norm_exceeds,
    },
    constants::*,
    encoding,
    hash_functions::{shake128, shake256},
    matrix::{
        add_vectors, compute_A_times_mask, compute_As1_plus_s2, compute_w_approx, subtract_vectors,
        vector_times_ring_element,
    },
    ntt::ntt,
    polynomial::PolynomialRingElement,
    pre_hash::{DomainSeparationContext, PreHash},
    sample::{sample_challenge_ring_element, sample_mask_vector},
    samplex4,
    simd::traits::Operations,
    utils::into_padded_array,
    MLDSASignature,
};

pub(crate) mod instantiations;
pub(crate) mod multiplexing;

pub(crate) struct Signature<
    SIMDUnit: Operations,
    const COMMITMENT_HASH_SIZE: usize,
    const COLUMNS_IN_A: usize,
    const ROWS_IN_A: usize,
> {
    pub commitment_hash: [u8; COMMITMENT_HASH_SIZE],
    pub signer_response: [PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
    pub hint: [[i32; COEFFICIENTS_IN_RING_ELEMENT]; ROWS_IN_A],
}

/// Generate a key pair.
pub(crate) fn generate_key_pair<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    Shake256: shake256::Xof,
    Shake256X4: shake256::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const ETA: usize,
    const ERROR_RING_ELEMENT_SIZE: usize,
    const SIGNING_KEY_SIZE: usize,
    const VERIFICATION_KEY_SIZE: usize,
>(
    randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
) -> ([u8; SIGNING_KEY_SIZE], [u8; VERIFICATION_KEY_SIZE]) {
    // 128 = SEED_FOR_A_SIZE + SEED_FOR_ERROR_VECTORS_SIZE + SEED_FOR_SIGNING_SIZE
    let mut seed_expanded = [0; 128];
    let mut shake = Shake256Absorb::new();
    shake.absorb(&randomness);
    let mut shake = shake.absorb_final(&[ROWS_IN_A as u8, COLUMNS_IN_A as u8]);
    shake.squeeze(&mut seed_expanded);

    let (seed_for_a, seed_expanded) = seed_expanded.split_at(SEED_FOR_A_SIZE);
    let (seed_for_error_vectors, seed_for_signing) =
        seed_expanded.split_at(SEED_FOR_ERROR_VECTORS_SIZE);

    let a_as_ntt = samplex4::matrix_A::<SIMDUnit, Shake128X4, ROWS_IN_A, COLUMNS_IN_A>(
        into_padded_array(seed_for_a),
    );

    let (s1, s2) = samplex4::sample_s1_and_s2::<SIMDUnit, Shake256X4, ETA, COLUMNS_IN_A, ROWS_IN_A>(
        into_padded_array(seed_for_error_vectors),
    );

    let t = compute_As1_plus_s2::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(&a_as_ntt, &s1, &s2);

    let (t0, t1) = power2round_vector::<SIMDUnit, ROWS_IN_A>(t);

    let verification_key_serialized = encoding::verification_key::generate_serialized::<
        SIMDUnit,
        ROWS_IN_A,
        VERIFICATION_KEY_SIZE,
    >(seed_for_a, t1);

    let signing_key_serialized = encoding::signing_key::generate_serialized::<
        SIMDUnit,
        Shake256,
        ROWS_IN_A,
        COLUMNS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
        SIGNING_KEY_SIZE,
    >(
        seed_for_a,
        seed_for_signing,
        &verification_key_serialized,
        s1,
        s2,
        t0,
    );

    (signing_key_serialized, verification_key_serialized)
}

#[derive(Debug)]
pub enum VerificationError {
    MalformedHintError,
    SignerResponseExceedsBoundError,
    CommitmentHashesDontMatchError,
    ContextTooLongError,
}

#[derive(Debug)]
pub enum SigningError {
    RejectionSamplingError,
    ContextTooLongError,
}

#[allow(non_snake_case)]
pub(crate) fn sign_pre_hashed<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    Shake256: shake256::Xof,
    Shake256X4: shake256::XofX4,
    PH: PreHash<PH_DIGEST_LEN>,
    const PH_DIGEST_LEN: usize,
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
    if context.len() > CONTEXT_MAX_LEN {
        return Err(SigningError::ContextTooLongError);
    }
    let pre_hashed_message = PH::hash(message);

    sign_internal::<
        SIMDUnit,
        Shake128X4,
        Shake256,
        Shake256X4,
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
    >(
        &signing_key,
        &pre_hashed_message,
        Some(DomainSeparationContext::new(context, Some(&PH::oid()))?),
        randomness,
    )
}

#[allow(non_snake_case)]
pub(crate) fn sign<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    Shake256: shake256::Xof,
    Shake256X4: shake256::XofX4,
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
    sign_internal::<
        SIMDUnit,
        Shake128X4,
        Shake256,
        Shake256X4,
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
    >(
        &signing_key,
        message,
        Some(DomainSeparationContext::new(context, None)?),
        randomness,
    )
}

/// The internal signing API.
///
/// If no `domain_separation_context` is supplied, it is assumed that
/// `message` already contains the domain separation.
#[allow(non_snake_case)]
pub(crate) fn sign_internal<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    Shake256: shake256::Xof,
    Shake256X4: shake256::XofX4,
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
    domain_separation_context: Option<DomainSeparationContext>,
    randomness: [u8; SIGNING_RANDOMNESS_SIZE],
) -> Result<MLDSASignature<SIGNATURE_SIZE>, SigningError> {
    let (seed_for_A, seed_for_signing, verification_key_hash, s1_as_ntt, s2_as_ntt, t0_as_ntt) =
        encoding::signing_key::deserialize_then_ntt::<
            SIMDUnit,
            ROWS_IN_A,
            COLUMNS_IN_A,
            ETA,
            ERROR_RING_ELEMENT_SIZE,
            SIGNING_KEY_SIZE,
        >(signing_key);

    let A_as_ntt = samplex4::matrix_A::<SIMDUnit, Shake128X4, ROWS_IN_A, COLUMNS_IN_A>(
        into_padded_array(&seed_for_A),
    );

    let mut message_representative = [0; MESSAGE_REPRESENTATIVE_SIZE];
    derive_message_representative(
        verification_key_hash,
        domain_separation_context,
        message,
        &mut message_representative,
    );

    let mut mask_seed = [0; MASK_SEED_SIZE];
    {
        let mut shake = Shake256Absorb::new();
        shake.absorb(&seed_for_signing);
        shake.absorb(&randomness);
        let mut shake = shake.absorb_final(&message_representative);

        shake.squeeze(&mut mask_seed);
    }

    let mut domain_separator_for_mask: u16 = 0;

    let BETA = (ONES_IN_VERIFIER_CHALLENGE * ETA) as i32;

    let mut attempt = 0;

    let mut commitment_hash = None;
    let mut signer_response = None;
    let mut hint = None;

    // As specified in [FIPS 204, Appendix C], the minimum number of
    // attempts in this rejection sampling loop is 814. This puts the
    // probability of failure at 2⁻²⁵⁶ or less.
    //
    // [FIPS 204, Appendix C]: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#appendix.C
    while attempt < REJECTION_SAMPLE_BOUND_SIGN {
        attempt += 1;

        let mask =
            sample_mask_vector::<SIMDUnit, Shake256, Shake256X4, COLUMNS_IN_A, GAMMA1_EXPONENT>(
                into_padded_array(&mask_seed),
                &mut domain_separator_for_mask,
            );

        let A_times_mask =
            compute_A_times_mask::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(&A_as_ntt, &mask);

        let (w0, commitment) = decompose_vector::<SIMDUnit, ROWS_IN_A, GAMMA2>(A_times_mask);

        let mut commitment_hash_candidate = [0; COMMITMENT_HASH_SIZE];
        {
            let commitment_serialized = encoding::commitment::serialize_vector::<
                SIMDUnit,
                ROWS_IN_A,
                COMMITMENT_RING_ELEMENT_SIZE,
                COMMITMENT_VECTOR_SIZE,
            >(commitment);

            let mut shake = Shake256Absorb::new();
            shake.absorb(&message_representative);
            let mut shake = shake.absorb_final(&commitment_serialized);

            shake.squeeze(&mut commitment_hash_candidate);
        }

        let verifier_challenge_as_ntt = ntt(sample_challenge_ring_element::<
            SIMDUnit,
            Shake256,
            ONES_IN_VERIFIER_CHALLENGE,
            COMMITMENT_HASH_SIZE,
        >(commitment_hash_candidate));

        let challenge_times_s1 = vector_times_ring_element::<SIMDUnit, COLUMNS_IN_A>(
            &s1_as_ntt,
            &verifier_challenge_as_ntt,
        );
        let challenge_times_s2 = vector_times_ring_element::<SIMDUnit, ROWS_IN_A>(
            &s2_as_ntt,
            &verifier_challenge_as_ntt,
        );

        let signer_response_candidate =
            add_vectors::<SIMDUnit, COLUMNS_IN_A>(&mask, &challenge_times_s1);

        let w0_minus_challenge_times_s2 =
            subtract_vectors::<SIMDUnit, ROWS_IN_A>(&w0, &challenge_times_s2);

        if vector_infinity_norm_exceeds::<SIMDUnit, COLUMNS_IN_A>(
            signer_response_candidate,
            (1 << GAMMA1_EXPONENT) - BETA,
        ) {
        } else {
            if vector_infinity_norm_exceeds::<SIMDUnit, ROWS_IN_A>(
                w0_minus_challenge_times_s2,
                GAMMA2 - BETA,
            ) {
            } else {
                let challenge_times_t0 = vector_times_ring_element::<SIMDUnit, ROWS_IN_A>(
                    &t0_as_ntt,
                    &verifier_challenge_as_ntt,
                );
                if vector_infinity_norm_exceeds::<SIMDUnit, ROWS_IN_A>(challenge_times_t0, GAMMA2) {
                } else {
                    let w0_minus_c_times_s2_plus_c_times_t0 = add_vectors::<SIMDUnit, ROWS_IN_A>(
                        &w0_minus_challenge_times_s2,
                        &challenge_times_t0,
                    );
                    let (hint_candidate, ones_in_hint) = make_hint::<SIMDUnit, ROWS_IN_A, GAMMA2>(
                        w0_minus_c_times_s2_plus_c_times_t0,
                        commitment,
                    );

                    if ones_in_hint > MAX_ONES_IN_HINT {
                    } else {
                        attempt = REJECTION_SAMPLE_BOUND_SIGN; // exit loop now
                        commitment_hash = Some(commitment_hash_candidate);
                        signer_response = Some(signer_response_candidate);
                        hint = Some(hint_candidate);
                    }
                }
            }
        }
    }

    let commitment_hash = match commitment_hash {
        Some(commitment_hash) => Ok(commitment_hash),
        None => Err(SigningError::RejectionSamplingError),
    }?;

    let signer_response = match signer_response {
        Some(signer_response) => Ok(signer_response),
        None => Err(SigningError::RejectionSamplingError),
    }?;

    let hint = match hint {
        Some(hint) => Ok(hint),
        None => Err(SigningError::RejectionSamplingError),
    }?;

    let signature = Signature::<SIMDUnit, COMMITMENT_HASH_SIZE, COLUMNS_IN_A, ROWS_IN_A> {
        commitment_hash,
        signer_response,
        hint,
    }
    .serialize::<GAMMA1_EXPONENT, GAMMA1_RING_ELEMENT_SIZE, MAX_ONES_IN_HINT, SIGNATURE_SIZE>();

    Ok(MLDSASignature(signature))
}

/// This corresponds to line 6 in algorithm 7 in FIPS 204 (line 7 in algorithm
/// 8, resp.).
///
/// If `domain_separation_context` is supplied, applies domain
/// separation and length encoding to the context string,
/// before appending the message (in the regular variant) or the
/// pre-hash OID as well as the pre-hashed message digest. Otherwise,
/// it is assumed that `message` already contains domain separation
/// information.
///
/// In FIPS 204 M' is the concatenation of the domain separated context, any
/// potential pre-hash OID and the message (or the message pre-hash). We do not
/// explicitely construct the concatenation in memory since it is of statically unknown
/// length, but feed its components directly into the incremental XOF.
///
/// Refer to line 10 of Algorithm 2 (and line 5 of Algorithm 3, resp.) in [FIPS
/// 204](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#section.5)
/// for details on the domain separation for regular ML-DSA. Line
/// 23 of Algorithm 4 (and line 18 of Algorithm 5,resp.) describe domain separation for the HashMl-DSA
/// variant.
fn derive_message_representative(
    verification_key_hash: [u8; 64],
    domain_separation_context: Option<DomainSeparationContext>,
    message: &[u8],
    message_representative: &mut [u8; 64],
) {
    let mut shake = Shake256Absorb::new();
    shake.absorb(&verification_key_hash);
    if let Some(domain_separation_context) = domain_separation_context {
        shake.absorb(&[domain_separation_context.pre_hash_oid().is_some() as u8]);
        shake.absorb(&[domain_separation_context.context().len() as u8]);
        shake.absorb(domain_separation_context.context());
        if let Some(pre_hash_oid) = domain_separation_context.pre_hash_oid() {
            shake.absorb(pre_hash_oid)
        }
    }

    let mut shake = shake.absorb_final(message);
    shake.squeeze(message_representative);
}

/// The internal verification API.
///
/// If no `domain_separation_context` is supplied, it is assumed that
/// `message` already contains the domain separation.
#[allow(non_snake_case)]
pub(crate) fn verify_internal<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    Shake256: shake256::Xof,
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
    domain_separation_context: Option<DomainSeparationContext>,
    signature_serialized: &[u8; SIGNATURE_SIZE],
) -> Result<(), VerificationError> {
    let (seed_for_A, t1) =
        encoding::verification_key::deserialize::<SIMDUnit, ROWS_IN_A, VERIFICATION_KEY_SIZE>(
            verification_key_serialized,
        );

    let signature =
        Signature::<SIMDUnit, COMMITMENT_HASH_SIZE, COLUMNS_IN_A, ROWS_IN_A>::deserialize::<
            GAMMA1_EXPONENT,
            GAMMA1_RING_ELEMENT_SIZE,
            MAX_ONES_IN_HINT,
            SIGNATURE_SIZE,
        >(signature_serialized)?;

    // We use if-else branches because early returns will not go through hax.
    if !vector_infinity_norm_exceeds::<SIMDUnit, COLUMNS_IN_A>(
        signature.signer_response,
        (2 << GAMMA1_EXPONENT) - BETA,
    ) {
        let A_as_ntt = samplex4::matrix_A::<SIMDUnit, Shake128X4, ROWS_IN_A, COLUMNS_IN_A>(
            into_padded_array(&seed_for_A),
        );

        let mut verification_key_hash = [0; BYTES_FOR_VERIFICATION_KEY_HASH];
        Shake256::shake256::<BYTES_FOR_VERIFICATION_KEY_HASH>(
            verification_key_serialized,
            &mut verification_key_hash,
        );
        let mut message_representative = [0; MESSAGE_REPRESENTATIVE_SIZE];
        derive_message_representative(
            verification_key_hash,
            domain_separation_context,
            message,
            &mut message_representative,
        );

        let verifier_challenge_as_ntt = ntt(sample_challenge_ring_element::<
            SIMDUnit,
            Shake256,
            ONES_IN_VERIFIER_CHALLENGE,
            COMMITMENT_HASH_SIZE,
        >(signature.commitment_hash));

        let w_approx = compute_w_approx::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
            &A_as_ntt,
            signature.signer_response,
            verifier_challenge_as_ntt,
            t1,
        );

        let mut commitment_hash = [0; COMMITMENT_HASH_SIZE];
        {
            let commitment = use_hint::<SIMDUnit, ROWS_IN_A, GAMMA2>(signature.hint, w_approx);
            let commitment_serialized = encoding::commitment::serialize_vector::<
                SIMDUnit,
                ROWS_IN_A,
                COMMITMENT_RING_ELEMENT_SIZE,
                COMMITMENT_VECTOR_SIZE,
            >(commitment);

            let mut shake = Shake256Absorb::new();
            shake.absorb(&message_representative);
            let mut shake = shake.absorb_final(&commitment_serialized);

            shake.squeeze(&mut commitment_hash);
        }

        if signature.commitment_hash != commitment_hash {
            Err(VerificationError::CommitmentHashesDontMatchError)
        } else {
            Ok(())
        }
    } else {
        Err(VerificationError::SignerResponseExceedsBoundError)
    }
}

#[allow(non_snake_case)]
pub(crate) fn verify<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    Shake256: shake256::Xof,
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
    verify_internal::<
        SIMDUnit,
        Shake128X4,
        Shake256,
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
        &verification_key_serialized,
        message,
        Some(DomainSeparationContext::new(context, None)?),
        &signature_serialized,
    )
}

#[allow(non_snake_case)]
pub(crate) fn verify_pre_hashed<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    Shake256: shake256::Xof,
    PH: PreHash<PH_DIGEST_LEN>,
    const PH_DIGEST_LEN: usize,
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
    let pre_hashed_message = PH::hash(message);

    verify_internal::<
        SIMDUnit,
        Shake128X4,
        Shake256,
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
        &verification_key_serialized,
        &pre_hashed_message,
        Some(DomainSeparationContext::new(context, Some(&PH::oid()))?),
        &signature_serialized,
    )
}
