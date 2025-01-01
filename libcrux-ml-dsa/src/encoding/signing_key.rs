use crate::{
    constants::{
        BYTES_FOR_VERIFICATION_KEY_HASH, RING_ELEMENT_OF_T0S_SIZE, SEED_FOR_A_SIZE,
        SEED_FOR_SIGNING_SIZE,
    },
    encoding,
    hash_functions::shake256,
    helper::cloop,
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[inline(always)]
pub(crate) fn generate_serialized<
    SIMDUnit: Operations,
    Shake256: shake256::DsaXof,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const ETA: usize,
    const ERROR_RING_ELEMENT_SIZE: usize,
>(
    seed_matrix: &[u8],
    seed_signing: &[u8],
    verification_key: &[u8],
    s1_2: &[PolynomialRingElement<SIMDUnit>],
    t0: [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
    signing_key_serialized: &mut [u8],
) {
    let mut offset = 0;

    signing_key_serialized[offset..offset + SEED_FOR_A_SIZE].copy_from_slice(seed_matrix);
    offset += SEED_FOR_A_SIZE;

    signing_key_serialized[offset..offset + SEED_FOR_SIGNING_SIZE].copy_from_slice(seed_signing);
    offset += SEED_FOR_SIGNING_SIZE;

    let mut verification_key_hash = [0; BYTES_FOR_VERIFICATION_KEY_HASH];
    Shake256::shake256::<BYTES_FOR_VERIFICATION_KEY_HASH>(
        verification_key,
        &mut verification_key_hash,
    );
    signing_key_serialized[offset..offset + BYTES_FOR_VERIFICATION_KEY_HASH]
        .copy_from_slice(&verification_key_hash);
    offset += BYTES_FOR_VERIFICATION_KEY_HASH;

    for i in 0..s1_2.len() {
        encoding::error::serialize::<SIMDUnit, ETA, ERROR_RING_ELEMENT_SIZE>(
            &s1_2[i],
            &mut signing_key_serialized[offset..offset + ERROR_RING_ELEMENT_SIZE],
        );
        offset += ERROR_RING_ELEMENT_SIZE;
    }

    cloop! {
        for ring_element in t0.iter() {
            encoding::t0::serialize::<SIMDUnit>(
                *ring_element,
                &mut signing_key_serialized[offset..offset + RING_ELEMENT_OF_T0S_SIZE],
            );
            offset += RING_ELEMENT_OF_T0S_SIZE;
        }
    }
}
