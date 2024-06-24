use crate::{
    arithmetic::{
        decompose_vector, make_hint_vector, power2round_vector, vector_infinity_norm_exceeds,
        PolynomialRingElement,
    },
    constants::*,
    encoding,
    hash_functions::H,
    matrix::{
        add_vectors, compute_A_times_mask, compute_As1_plus_s2, expand_to_A, subtract_vectors,
        vector_times_ring_element,
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
#[inline(always)]
pub(super) fn generate_serialized_signature<
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const COMMITMENT_HASH_SIZE: usize,
    const GAMMA1_EXPONENT: usize,
    const GAMMA1_RING_ELEMENT_SIZE: usize,
    const MAX_ONES_IN_HINT: usize,
    const SIGNATURE_SIZE: usize,
>(
    commitment_hash: [u8; COMMITMENT_HASH_SIZE],
    signer_response: [PolynomialRingElement; COLUMNS_IN_A],
    hint_vector: [[bool; COEFFICIENTS_IN_RING_ELEMENT]; ROWS_IN_A],
) -> [u8; SIGNATURE_SIZE] {
    let mut signature = [0u8; SIGNATURE_SIZE];
    let mut offset = 0;

    signature[offset..offset + COMMITMENT_HASH_SIZE].copy_from_slice(&commitment_hash);
    offset += COMMITMENT_HASH_SIZE;

    for i in 0..COLUMNS_IN_A {
        signature[offset..offset + GAMMA1_RING_ELEMENT_SIZE].copy_from_slice(
            &encoding::gamma1::serialize::<GAMMA1_EXPONENT, GAMMA1_RING_ELEMENT_SIZE>(
                signer_response[i],
            ),
        );
        offset += GAMMA1_RING_ELEMENT_SIZE;
    }

    for i in offset..offset + (MAX_ONES_IN_HINT + ROWS_IN_A) {
        signature[i] = 0;
    }

    let mut one_count = 0;
    let hint_serialized = &mut signature[offset..];

    for i in 0..ROWS_IN_A {
        for (j, hint) in hint_vector[i].into_iter().enumerate() {
            if hint == true {
                hint_serialized[one_count] = j as u8;
                one_count += 1;
            }
        }
        hint_serialized[MAX_ONES_IN_HINT + i] = one_count as u8;
    }

    signature
}

#[allow(non_snake_case)]
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

    let mut domain_separator_for_mask: u16 = 0;

    let BETA = (ONES_IN_VERIFIER_CHALLENGE * ETA) as i32;

    let mut attempt = 0;

    let (commitment_hash, signer_response, hint_vector) = loop {
        attempt += 1;
        if attempt >= 576 {
            // Depending on the mode, one try has a chance between 1/7 and 1/4
            // of succeeding.  Thus it is safe to say that 576 iterations
            // are enough as (6/7)⁵⁷⁶ < 2⁻¹²⁸[1].
            //
            // [1]: https://github.com/cloudflare/circl/blob/main/sign/dilithium/mode2/internal/dilithium.go#L341
            panic!("At least 576 signing attempts were made; this should only happen 1 in 2^{{128}} times: something is wrong.")
        }

        let mask = sample_mask_vector::<COLUMNS_IN_A, GAMMA1_EXPONENT>(
            into_padded_array(&mask_seed),
            &mut domain_separator_for_mask,
        );

        let A_times_mask = compute_A_times_mask(&A_as_ntt, &mask);

        let (w0, commitment) = decompose_vector::<ROWS_IN_A, GAMMA2>(A_times_mask);

        let commitment_hash: [u8; COMMITMENT_HASH_SIZE] = {
            let commitment_encoded = encoding::commitment::serialize_vector::<
                ROWS_IN_A,
                COMMITMENT_RING_ELEMENT_SIZE,
                COMMITMENT_VECTOR_SIZE,
            >(commitment);

            let mut hash_input = message_representative.to_vec();
            hash_input.extend_from_slice(&commitment_encoded);

            H::<COMMITMENT_HASH_SIZE>(&hash_input[..])
        };

        let verifier_challenge_as_ntt =
            ntt(sample_challenge_ring_element::<ONES_IN_VERIFIER_CHALLENGE>(
                commitment_hash[0..VERIFIER_CHALLENGE_SEED_SIZE]
                    .try_into()
                    .unwrap(),
            ));

        let challenge_times_s1 =
            vector_times_ring_element::<COLUMNS_IN_A>(&s1_as_ntt, &verifier_challenge_as_ntt);
        let challenge_times_s2 =
            vector_times_ring_element::<ROWS_IN_A>(&s2_as_ntt, &verifier_challenge_as_ntt);

        let signer_response = add_vectors::<COLUMNS_IN_A>(&mask, &challenge_times_s1);

        let w0_minus_challenge_times_s2 = subtract_vectors::<ROWS_IN_A>(&w0, &challenge_times_s2);

        if vector_infinity_norm_exceeds::<COLUMNS_IN_A>(
            signer_response,
            (1 << GAMMA1_EXPONENT) - BETA,
        ) {
            continue;
        }
        if vector_infinity_norm_exceeds::<ROWS_IN_A>(w0_minus_challenge_times_s2, GAMMA2 - BETA) {
            continue;
        }

        let challenge_times_t0 =
            vector_times_ring_element::<ROWS_IN_A>(&t0_as_ntt, &verifier_challenge_as_ntt);
        if vector_infinity_norm_exceeds::<ROWS_IN_A>(challenge_times_t0, GAMMA2) {
            continue;
        }

        let w0_minus_c_times_s2_plus_c_times_t0 =
            add_vectors::<ROWS_IN_A>(&w0_minus_challenge_times_s2, &challenge_times_t0);
        let (hint_vector, ones_in_hint) =
            make_hint_vector::<ROWS_IN_A, GAMMA2>(w0_minus_c_times_s2_plus_c_times_t0, commitment);
        if ones_in_hint > MAX_ONES_IN_HINT {
            continue;
        }

        break (commitment_hash, signer_response, hint_vector);
    };

    generate_serialized_signature::<
        ROWS_IN_A,
        COLUMNS_IN_A,
        COMMITMENT_HASH_SIZE,
        GAMMA1_EXPONENT,
        GAMMA1_RING_ELEMENT_SIZE,
        MAX_ONES_IN_HINT,
        SIGNATURE_SIZE,
    >(commitment_hash, signer_response, hint_vector)
}
