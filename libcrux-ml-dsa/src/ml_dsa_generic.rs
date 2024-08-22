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
    sample::{sample_challenge_ring_element, sample_mask_vector},
    samplex4,
    simd::traits::Operations,
    utils::into_padded_array,
    MLDSASignature,
};

pub(crate) mod instantiations;

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
    Shake256::shake256::<128>(&randomness, &mut seed_expanded);

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
    randomness: [u8; SIGNING_RANDOMNESS_SIZE],
) -> MLDSASignature<SIGNATURE_SIZE> {
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
    {
        let mut shake = Shake256Absorb::new();
        shake.absorb(&verification_key_hash);
        let mut shake = shake.absorb_final(message);

        shake.squeeze(&mut message_representative);
    }

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

    // TODO: This style of rejection sampling, with the break and the continues,
    // won't pass through hax; it'll need to be rewritten.
    // See https://github.com/cryspen/libcrux/issues/341
    let (commitment_hash, signer_response, hint) = loop {
        attempt += 1;

        // Depending on the mode, one try has a chance between 1/7 and 1/4
        // of succeeding.  Thus it is safe to say that 576 iterations
        // are enough as (6/7)⁵⁷⁶ < 2⁻¹²⁸[1].
        //
        // [1]: https://github.com/cloudflare/circl/blob/main/sign/dilithium/mode2/internal/dilithium.go#L341
        debug_assert!(attempt < 576);

        let mask =
            sample_mask_vector::<SIMDUnit, Shake256, Shake256X4, COLUMNS_IN_A, GAMMA1_EXPONENT>(
                into_padded_array(&mask_seed),
                &mut domain_separator_for_mask,
            );

        let A_times_mask =
            compute_A_times_mask::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(&A_as_ntt, &mask);

        let (w0, commitment) = decompose_vector::<SIMDUnit, ROWS_IN_A, GAMMA2>(A_times_mask);

        let mut commitment_hash = [0; COMMITMENT_HASH_SIZE];
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

            shake.squeeze(&mut commitment_hash);
        }

        let verifier_challenge_as_ntt = ntt(sample_challenge_ring_element::<
            SIMDUnit,
            Shake256,
            ONES_IN_VERIFIER_CHALLENGE,
        >(
            commitment_hash[0..VERIFIER_CHALLENGE_SEED_SIZE]
                .try_into()
                .unwrap(),
        ));

        let challenge_times_s1 = vector_times_ring_element::<SIMDUnit, COLUMNS_IN_A>(
            &s1_as_ntt,
            &verifier_challenge_as_ntt,
        );
        let challenge_times_s2 = vector_times_ring_element::<SIMDUnit, ROWS_IN_A>(
            &s2_as_ntt,
            &verifier_challenge_as_ntt,
        );

        let signer_response = add_vectors::<SIMDUnit, COLUMNS_IN_A>(&mask, &challenge_times_s1);

        let w0_minus_challenge_times_s2 =
            subtract_vectors::<SIMDUnit, ROWS_IN_A>(&w0, &challenge_times_s2);

        if vector_infinity_norm_exceeds::<SIMDUnit, COLUMNS_IN_A>(
            signer_response,
            (1 << GAMMA1_EXPONENT) - BETA,
        ) {
            continue;
        }
        if vector_infinity_norm_exceeds::<SIMDUnit, ROWS_IN_A>(
            w0_minus_challenge_times_s2,
            GAMMA2 - BETA,
        ) {
            continue;
        }

        let challenge_times_t0 = vector_times_ring_element::<SIMDUnit, ROWS_IN_A>(
            &t0_as_ntt,
            &verifier_challenge_as_ntt,
        );
        if vector_infinity_norm_exceeds::<SIMDUnit, ROWS_IN_A>(challenge_times_t0, GAMMA2) {
            continue;
        }

        let w0_minus_c_times_s2_plus_c_times_t0 =
            add_vectors::<SIMDUnit, ROWS_IN_A>(&w0_minus_challenge_times_s2, &challenge_times_t0);
        let (hint, ones_in_hint) = make_hint::<SIMDUnit, ROWS_IN_A, GAMMA2>(
            w0_minus_c_times_s2_plus_c_times_t0,
            commitment,
        );
        if ones_in_hint > MAX_ONES_IN_HINT {
            continue;
        }

        break (commitment_hash, signer_response, hint);
    };

    let signature = Signature::<SIMDUnit, COMMITMENT_HASH_SIZE, COLUMNS_IN_A, ROWS_IN_A> {
        commitment_hash,
        signer_response,
        hint,
    }
    .serialize::<GAMMA1_EXPONENT, GAMMA1_RING_ELEMENT_SIZE, MAX_ONES_IN_HINT, SIGNATURE_SIZE>();

    MLDSASignature(signature)
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
        {
            let mut shake = Shake256Absorb::new();
            shake.absorb(&verification_key_hash);
            let mut shake = shake.absorb_final(&message);

            shake.squeeze(&mut message_representative);
        };

        let verifier_challenge_as_ntt = ntt(sample_challenge_ring_element::<
            SIMDUnit,
            Shake256,
            ONES_IN_VERIFIER_CHALLENGE,
        >(
            signature.commitment_hash[0..VERIFIER_CHALLENGE_SEED_SIZE]
                .try_into()
                .unwrap(),
        ));

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
