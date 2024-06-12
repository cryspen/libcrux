use crate::{
    arithmetic::{decompose_vector, power2round_vector, PolynomialRingElement},
    commitment,
    constants::*,
    encoding,
    hash_functions::H,
    matrix::{
        add_vectors, compute_A_times_mask, compute_As1_plus_s2, compute_challenge_times_error,
        expand_to_A, subtract_vectors,
    },
    ntt::ntt,
    sample::{sample_challenge_ring_element, sample_error_vector, sample_mask_vector},
    utils::into_padded_array,
};

#[allow(non_snake_case)]
#[inline(always)]
pub(super) fn generate_serialized_verification_key<
    const ROWS_IN_A: usize,
    const VERIFICATION_KEY_SIZE: usize,
>(
    seed_for_A: &[u8],
    t1: [PolynomialRingElement; ROWS_IN_A],
) -> [u8; VERIFICATION_KEY_SIZE] {
    let mut verification_key_serialized = [0u8; VERIFICATION_KEY_SIZE];
    verification_key_serialized[0..SEED_FOR_A_SIZE].copy_from_slice(&seed_for_A);

    for i in 0..ROWS_IN_A {
        let offset = SEED_FOR_A_SIZE + (i * RING_ELEMENT_OF_T1S_SIZE);
        verification_key_serialized[offset..offset + RING_ELEMENT_OF_T1S_SIZE]
            .copy_from_slice(&encoding::t1::serialize(t1[i]));
    }

    verification_key_serialized
}

#[allow(non_snake_case)]
#[inline(always)]
pub(super) fn generate_serialized_signing_key<
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const ETA: usize,
    const ERROR_RING_ELEMENT_SIZE: usize,
    const SIGNING_KEY_SIZE: usize,
>(
    seed_for_A: &[u8],
    seed_for_signing: &[u8],
    verification_key: &[u8],
    s1: [PolynomialRingElement; COLUMNS_IN_A],
    s2: [PolynomialRingElement; ROWS_IN_A],
    t0: [PolynomialRingElement; ROWS_IN_A],
) -> [u8; SIGNING_KEY_SIZE] {
    let mut signing_key_serialized = [0u8; SIGNING_KEY_SIZE];
    let mut offset = 0;

    signing_key_serialized[offset..offset + SEED_FOR_A_SIZE].copy_from_slice(&seed_for_A);
    offset += SEED_FOR_A_SIZE;

    signing_key_serialized[offset..offset + SEED_FOR_SIGNING_SIZE]
        .copy_from_slice(&seed_for_signing);
    offset += SEED_FOR_SIGNING_SIZE;

    let verification_key_hash = H::<BYTES_FOR_VERIFICATION_KEY_HASH>(verification_key);
    signing_key_serialized[offset..offset + BYTES_FOR_VERIFICATION_KEY_HASH]
        .copy_from_slice(&verification_key_hash);
    offset += BYTES_FOR_VERIFICATION_KEY_HASH;

    for i in 0..COLUMNS_IN_A {
        signing_key_serialized[offset..offset + ERROR_RING_ELEMENT_SIZE].copy_from_slice(
            &encoding::error::serialize::<ETA, ERROR_RING_ELEMENT_SIZE>(s1[i]),
        );
        offset += ERROR_RING_ELEMENT_SIZE;
    }

    for i in 0..ROWS_IN_A {
        signing_key_serialized[offset..offset + ERROR_RING_ELEMENT_SIZE].copy_from_slice(
            &encoding::error::serialize::<ETA, ERROR_RING_ELEMENT_SIZE>(s2[i]),
        );
        offset += ERROR_RING_ELEMENT_SIZE;
    }

    for i in 0..ROWS_IN_A {
        signing_key_serialized[offset..offset + RING_ELEMENT_OF_T0S_SIZE]
            .copy_from_slice(&encoding::t0::serialize(t0[i]));
        offset += RING_ELEMENT_OF_T0S_SIZE;
    }

    signing_key_serialized
}

#[allow(non_snake_case)]
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
    let seed_expanded = H::<128>(&randomness);
    let (seed_for_A, seed_expanded) = seed_expanded.split_at(SEED_FOR_A_SIZE);
    let (seed_for_error_vectors, seed_for_signing) =
        seed_expanded.split_at(SEED_FOR_ERROR_VECTORS_SIZE);

    let mut domain_separator: u16 = 0;

    let A_as_ntt = expand_to_A::<ROWS_IN_A, COLUMNS_IN_A>(into_padded_array(seed_for_A));

    let s1 = sample_error_vector::<COLUMNS_IN_A, ETA>(
        into_padded_array(seed_for_error_vectors),
        &mut domain_separator,
    );
    let s2 = sample_error_vector::<ROWS_IN_A, ETA>(
        into_padded_array(seed_for_error_vectors),
        &mut domain_separator,
    );

    let t = compute_As1_plus_s2::<ROWS_IN_A, COLUMNS_IN_A>(&A_as_ntt, &s1, &s2);

    let (t0, t1) = power2round_vector::<ROWS_IN_A>(t);

    let verification_key_serialized =
        generate_serialized_verification_key::<ROWS_IN_A, VERIFICATION_KEY_SIZE>(seed_for_A, t1);

    let signing_key_serialized = generate_serialized_signing_key::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
        SIGNING_KEY_SIZE,
    >(
        seed_for_A,
        seed_for_signing,
        &verification_key_serialized,
        s1,
        s2,
        t0,
    );

    (signing_key_serialized, verification_key_serialized)
}

#[allow(non_snake_case)]
pub(crate) fn sign<
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const ETA: usize,
    const ERROR_RING_ELEMENT_SIZE: usize,
    const GAMMA1_EXPONENT: usize,
    const ALPHA: i32,
    const COMMITMENT_RING_ELEMENT_SIZE: usize,
    const COMMITMENT_VECTOR_SIZE: usize,
    const COMMITMENT_HASH_SIZE: usize,
    const NUMBER_OF_ONES_IN_VERIFIER_CHALLENGE: usize,
    const SIGNING_KEY_SIZE: usize,
    const SIGNATURE_SIZE: usize,
>(
    signing_key: [u8; SIGNING_KEY_SIZE],
    message: &[u8],
    randomness: [u8; SIGNING_RANDOMNESS_SIZE],
) -> [u8; SIGNATURE_SIZE] {
    let (seed_for_A, remaining_signing_key) = signing_key.split_at(SEED_FOR_A_SIZE);
    let (seed_for_signing, remaining_signing_key) =
        remaining_signing_key.split_at(SEED_FOR_SIGNING_SIZE);
    let (verification_key_hash, remaining_signing_key) =
        remaining_signing_key.split_at(BYTES_FOR_VERIFICATION_KEY_HASH);

    let (s1_serialized, remaining_signing_key) =
        remaining_signing_key.split_at(ERROR_RING_ELEMENT_SIZE * COLUMNS_IN_A);
    let (s2_serialized, t0_serialized) =
        remaining_signing_key.split_at(ERROR_RING_ELEMENT_SIZE * ROWS_IN_A);

    let s1_as_ntt = encoding::error::deserialize_to_vector_then_ntt::<
        COLUMNS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
    >(s1_serialized);
    let s2_as_ntt =
        encoding::error::deserialize_to_vector_then_ntt::<ROWS_IN_A, ETA, ERROR_RING_ELEMENT_SIZE>(
            s2_serialized,
        );

    let t0_as_ntt = encoding::t0::deserialize_to_vector_then_ntt::<ROWS_IN_A>(t0_serialized);

    let A_as_ntt = expand_to_A::<ROWS_IN_A, COLUMNS_IN_A>(into_padded_array(seed_for_A));

    let message_representative = {
        let mut hash_input = verification_key_hash.to_vec();
        hash_input.extend_from_slice(message);

        H::<MESSAGE_REPRESENTATIVE_SIZE>(&hash_input[..])
    };

    let mask_seed: [u8; MASK_SEED_SIZE] = {
        let mut hash_input = seed_for_signing.to_vec();
        hash_input.extend_from_slice(&randomness);
        hash_input.extend_from_slice(&message_representative);

        H::<MASK_SEED_SIZE>(&hash_input[..])
    };

    let invalid_signatures: u16 = 0;
    let mut domain_separator_for_mask: u16 = 0;

    loop {
        let mask = sample_mask_vector::<COLUMNS_IN_A, GAMMA1_EXPONENT>(
            into_padded_array(&mask_seed),
            &mut domain_separator_for_mask,
        );

        let A_times_mask = compute_A_times_mask(&A_as_ntt, &mask);

        let (w0, commitment) = decompose_vector::<ROWS_IN_A, ALPHA>(A_times_mask);

        let verifier_challenge_seed: [u8; 32] = {
            let commitment_encoded = commitment::encode_vector::<
                ROWS_IN_A,
                COMMITMENT_RING_ELEMENT_SIZE,
                COMMITMENT_VECTOR_SIZE,
            >(commitment);

            let mut hash_input = message_representative.to_vec();
            hash_input.extend_from_slice(&commitment_encoded);

            (&H::<COMMITMENT_HASH_SIZE>(&hash_input[..])[0..32])
                .try_into()
                .unwrap()
        };

        let verifier_challenge_as_ntt = ntt(sample_challenge_ring_element::<
            NUMBER_OF_ONES_IN_VERIFIER_CHALLENGE,
        >(verifier_challenge_seed));

        let challenge_times_s1 =
            compute_challenge_times_error::<COLUMNS_IN_A>(&verifier_challenge_as_ntt, &s1_as_ntt);
        let challenge_times_s2 =
            compute_challenge_times_error::<ROWS_IN_A>(&verifier_challenge_as_ntt, &s2_as_ntt);

        let signer_response = add_vectors::<COLUMNS_IN_A>(&mask, &challenge_times_s1);

        let w0_minus_challenge_times_s2 = subtract_vectors::<ROWS_IN_A>(&w0, &challenge_times_s2);
    }
}
