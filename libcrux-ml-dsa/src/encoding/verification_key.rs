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
                .copy_from_slice(&t1::serialize::<SIMDUnit>(ring_element));
        }
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

#[inline(always)]
pub(crate) fn deserialize<SIMDUnit: Operations>(
    rows_in_a: usize,
    verification_key_size: usize,
    serialized: &[u8],
    t1: &mut [PolynomialRingElement<SIMDUnit>],
) {
    debug_assert!(serialized.len() == verification_key_size - SEED_FOR_A_SIZE);

    for i in 0..rows_in_a {
        t1::deserialize::<SIMDUnit>(
            &serialized[i * RING_ELEMENT_OF_T1S_SIZE..(i + 1) * RING_ELEMENT_OF_T1S_SIZE],
            &mut t1[i],
        );
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}
