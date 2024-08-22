use crate::{
    constants::{
        BYTES_FOR_VERIFICATION_KEY_HASH, RING_ELEMENT_OF_T0S_SIZE, SEED_FOR_A_SIZE,
        SEED_FOR_SIGNING_SIZE,
    },
    encoding,
    hash_functions::shake256,
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn generate_serialized<
    SIMDUnit: Operations,
    Shake256: shake256::Xof,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const ETA: usize,
    const ERROR_RING_ELEMENT_SIZE: usize,
    const SIGNING_KEY_SIZE: usize,
>(
    seed_for_A: &[u8],
    seed_for_signing: &[u8],
    verification_key: &[u8],
    s1: [PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
    s2: [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
    t0: [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
) -> [u8; SIGNING_KEY_SIZE] {
    let mut signing_key_serialized = [0u8; SIGNING_KEY_SIZE];
    let mut offset = 0;

    signing_key_serialized[offset..offset + SEED_FOR_A_SIZE].copy_from_slice(seed_for_A);
    offset += SEED_FOR_A_SIZE;

    signing_key_serialized[offset..offset + SEED_FOR_SIGNING_SIZE]
        .copy_from_slice(seed_for_signing);
    offset += SEED_FOR_SIGNING_SIZE;

    let mut verification_key_hash = [0; BYTES_FOR_VERIFICATION_KEY_HASH];
    Shake256::shake256::<BYTES_FOR_VERIFICATION_KEY_HASH>(
        verification_key,
        &mut verification_key_hash,
    );
    signing_key_serialized[offset..offset + BYTES_FOR_VERIFICATION_KEY_HASH]
        .copy_from_slice(&verification_key_hash);
    offset += BYTES_FOR_VERIFICATION_KEY_HASH;

    for ring_element in s1.iter() {
        signing_key_serialized[offset..offset + ERROR_RING_ELEMENT_SIZE].copy_from_slice(
            &encoding::error::serialize::<SIMDUnit, ETA, ERROR_RING_ELEMENT_SIZE>(*ring_element),
        );
        offset += ERROR_RING_ELEMENT_SIZE;
    }

    for ring_element in s2.iter() {
        signing_key_serialized[offset..offset + ERROR_RING_ELEMENT_SIZE].copy_from_slice(
            &encoding::error::serialize::<SIMDUnit, ETA, ERROR_RING_ELEMENT_SIZE>(*ring_element),
        );
        offset += ERROR_RING_ELEMENT_SIZE;
    }

    for ring_element in t0.iter() {
        signing_key_serialized[offset..offset + RING_ELEMENT_OF_T0S_SIZE]
            .copy_from_slice(&encoding::t0::serialize::<SIMDUnit>(*ring_element));
        offset += RING_ELEMENT_OF_T0S_SIZE;
    }

    signing_key_serialized
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn deserialize_then_ntt<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const ETA: usize,
    const ERROR_RING_ELEMENT_SIZE: usize,
    const SIGNING_KEY_SIZE: usize,
>(
    serialized: &[u8; SIGNING_KEY_SIZE],
) -> (
    [u8; SEED_FOR_A_SIZE],                           // seed_for_A
    [u8; SEED_FOR_SIGNING_SIZE],                     // seed_for_signing
    [u8; BYTES_FOR_VERIFICATION_KEY_HASH],           // verification_key_hash
    [PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A], // s1
    [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],    // s2
    [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],    // t0_as_ntt
) {
    let (seed_for_A, remaining_serialized) = serialized.split_at(SEED_FOR_A_SIZE);
    let (seed_for_signing, remaining_serialized) =
        remaining_serialized.split_at(SEED_FOR_SIGNING_SIZE);
    let (verification_key_hash, remaining_serialized) =
        remaining_serialized.split_at(BYTES_FOR_VERIFICATION_KEY_HASH);

    let (s1_serialized, remaining_serialized) =
        remaining_serialized.split_at(ERROR_RING_ELEMENT_SIZE * COLUMNS_IN_A);
    let (s2_serialized, t0_serialized) =
        remaining_serialized.split_at(ERROR_RING_ELEMENT_SIZE * ROWS_IN_A);

    let s1_as_ntt = encoding::error::deserialize_to_vector_then_ntt::<
        SIMDUnit,
        COLUMNS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
    >(s1_serialized);
    let s2_as_ntt = encoding::error::deserialize_to_vector_then_ntt::<
        SIMDUnit,
        ROWS_IN_A,
        ETA,
        ERROR_RING_ELEMENT_SIZE,
    >(s2_serialized);

    let t0_as_ntt =
        encoding::t0::deserialize_to_vector_then_ntt::<SIMDUnit, ROWS_IN_A>(t0_serialized);

    (
        seed_for_A.try_into().unwrap(),
        seed_for_signing.try_into().unwrap(),
        verification_key_hash.try_into().unwrap(),
        s1_as_ntt,
        s2_as_ntt,
        t0_as_ntt,
    )
}
