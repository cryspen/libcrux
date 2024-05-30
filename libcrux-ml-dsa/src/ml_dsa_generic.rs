use crate::{
    arithmetic::{power2round_vector, PolynomialRingElement},
    constants::{BYTES_IN_RING_ELEMENT_OF_T1S, SEED_FOR_A_SIZE, SEED_FOR_ERROR_VECTORS_SIZE},
    hash_functions::H,
    matrix::{compute_As1_plus_s2, expand_to_A, sample_error_vector},
    serialize::serialize_ring_element_of_t1s,
    utils::into_padded_array,
};

#[allow(non_snake_case)]
#[inline(always)]
pub(super) fn serialize_verification_key<
    const ROWS_IN_A: usize,
    const VERIFICATION_KEY_SIZE: usize,
>(
    seed_for_A: &[u8],
    t1: [PolynomialRingElement; ROWS_IN_A],
) -> [u8; VERIFICATION_KEY_SIZE] {
    let mut verification_key_serialized = [0u8; VERIFICATION_KEY_SIZE];
    verification_key_serialized[0..SEED_FOR_A_SIZE].copy_from_slice(&seed_for_A);

    for i in 0..ROWS_IN_A {
        let offset = SEED_FOR_A_SIZE + (i * BYTES_IN_RING_ELEMENT_OF_T1S);
        verification_key_serialized[offset..offset + BYTES_IN_RING_ELEMENT_OF_T1S]
            .copy_from_slice(&serialize_ring_element_of_t1s(t1[i]));
    }

    verification_key_serialized
}

#[allow(non_snake_case)]
pub(crate) fn generate_key_pair<
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const ETA: usize,
    const SIGNING_KEY_SIZE: usize,
    const VERIFICATION_KEY_SIZE: usize,
>(
    randomness: [u8; 32],
) -> ([u8; SIGNING_KEY_SIZE], [u8; VERIFICATION_KEY_SIZE]) {
    let seed_expanded = H::<1024>(&randomness);
    let (seed_for_A, seed_expanded) = seed_expanded.split_at(SEED_FOR_A_SIZE);
    let (seed_for_error_vectors, _random_seed_for_signing) =
        seed_expanded.split_at(SEED_FOR_ERROR_VECTORS_SIZE);

    let mut domain_separator: u16 = 0;

    let A_as_ntt = expand_to_A::<ROWS_IN_A, COLUMNS_IN_A>(into_padded_array(seed_for_A), false);

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
        serialize_verification_key::<ROWS_IN_A, VERIFICATION_KEY_SIZE>(seed_for_A, t1);
    let signing_key_serialized = [0u8; SIGNING_KEY_SIZE];

    (signing_key_serialized, verification_key_serialized)
}
