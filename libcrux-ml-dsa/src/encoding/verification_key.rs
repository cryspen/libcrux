use crate::{
    constants::{RING_ELEMENT_OF_T1S_SIZE, SEED_FOR_A_SIZE},
    encoding::t1,
    helper::cloop,
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[inline(always)]
pub(crate) fn generate_serialized<SIMDUnit: Operations>(
    seed: &[u8],
    t1: &[PolynomialRingElement<SIMDUnit>],
    verification_key_serialized: &mut [u8],
) {
    verification_key_serialized[0..SEED_FOR_A_SIZE].copy_from_slice(seed);

    cloop! {
        for (i, ring_element) in t1.iter().enumerate() {
            let offset = SEED_FOR_A_SIZE + (i * RING_ELEMENT_OF_T1S_SIZE);
            verification_key_serialized[offset..offset + RING_ELEMENT_OF_T1S_SIZE]
                .copy_from_slice(&t1::serialize::<SIMDUnit>(*ring_element));
        }
    }
}

#[inline(always)]
pub(crate) fn deserialize<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const VERIFICATION_KEY_SIZE: usize,
>(
    serialized: &[u8],
    t1: &mut [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
) {
    debug_assert!(serialized.len() == VERIFICATION_KEY_SIZE - SEED_FOR_A_SIZE);

    for i in 0..ROWS_IN_A {
        t1::deserialize::<SIMDUnit>(
            &serialized[i * RING_ELEMENT_OF_T1S_SIZE..(i + 1) * RING_ELEMENT_OF_T1S_SIZE],
            &mut t1[i],
        );
    }
}
