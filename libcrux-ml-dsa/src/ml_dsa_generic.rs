use crate::{
    arithmetic::PolynomialRingElement,
    constants::{
        BYTES_FOR_RING_ELEMENT_OF_T0S, BYTES_FOR_RING_ELEMENT_OF_T1S,
        BYTES_FOR_VERIFICATION_KEY_HASH, SEED_FOR_A_SIZE, SEED_FOR_ERROR_VECTORS_SIZE,
        SEED_FOR_SIGNING_SIZE,
    },
    hash_functions::H,
    matrix::{compute_As1_plus_s2, expand_to_A, power2round_vector, sample_error_vector},
    serialize::{
        serialize_error_ring_element, serialize_ring_element_of_t0s, serialize_ring_element_of_t1s,
    },
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
        let offset = SEED_FOR_A_SIZE + (i * BYTES_FOR_RING_ELEMENT_OF_T1S);
        verification_key_serialized[offset..offset + BYTES_FOR_RING_ELEMENT_OF_T1S]
            .copy_from_slice(&serialize_ring_element_of_t1s(t1[i]));
    }

    verification_key_serialized
}

#[allow(non_snake_case)]
#[inline(always)]
pub(super) fn generate_serialized_signing_key<
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const ETA: usize,
    const BYTES_FOR_ERROR_RING_ELEMENT: usize,
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
        signing_key_serialized[offset..offset + BYTES_FOR_ERROR_RING_ELEMENT].copy_from_slice(
            &serialize_error_ring_element::<ETA, BYTES_FOR_ERROR_RING_ELEMENT>(s1[i]),
        );
        offset += BYTES_FOR_ERROR_RING_ELEMENT;
    }

    for i in 0..ROWS_IN_A {
        signing_key_serialized[offset..offset + BYTES_FOR_ERROR_RING_ELEMENT].copy_from_slice(
            &serialize_error_ring_element::<ETA, BYTES_FOR_ERROR_RING_ELEMENT>(s2[i]),
        );
        offset += BYTES_FOR_ERROR_RING_ELEMENT;
    }

    for i in 0..ROWS_IN_A {
        signing_key_serialized[offset..offset + BYTES_FOR_RING_ELEMENT_OF_T0S]
            .copy_from_slice(&serialize_ring_element_of_t0s(t0[i]));
        offset += BYTES_FOR_RING_ELEMENT_OF_T0S;
    }

    signing_key_serialized
}

#[allow(non_snake_case)]
pub(crate) fn generate_key_pair<
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const ETA: usize,
    const BYTES_FOR_ERROR_RING_ELEMENT: usize,
    const SIGNING_KEY_SIZE: usize,
    const VERIFICATION_KEY_SIZE: usize,
>(
    randomness: [u8; 32],
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
        BYTES_FOR_ERROR_RING_ELEMENT,
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
    const BYTES_FOR_ERROR_RING_ELEMENT: usize,
    const SIGNING_KEY_SIZE: usize,
    const SIGNATURE_SIZE: usize,
>(
    signing_key: [u8; SIGNING_KEY_SIZE],
    message: &[u8],
    randomness: [u8; 32],
) -> [u8; SIGNATURE_SIZE] {
    let (rho, remaining_signing_key) = signing_key.split_at(SEED_FOR_A_SIZE);
    let (seed_for_signing, remaining_signing_key) =
        remaining_signing_key.split_at(SEED_FOR_SIGNING_SIZE);
    let (verification_key_hash, remaining_signing_key) =
        remaining_signing_key.split_at(BYTES_FOR_VERIFICATION_KEY_HASH);

    let (s1_serialized, remaining_signing_key) =
        remaining_signing_key.split_at(BYTES_FOR_ERROR_RING_ELEMENT);
    let (s2_serializd, t0_serialized) =
        remaining_signing_key.split_at(BYTES_FOR_ERROR_RING_ELEMENT);

    todo!();
}
