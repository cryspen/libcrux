use crate::{
    arithmetic::PolynomialRingElement,
    constants::{
        BYTES_FOR_VERIFICATION_KEY_HASH, RING_ELEMENT_OF_T0S_SIZE, SEED_FOR_A_SIZE,
        SEED_FOR_SIGNING_SIZE,
    },
    encoding,
    hash_functions::H,
};

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn generate_serialized<
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
