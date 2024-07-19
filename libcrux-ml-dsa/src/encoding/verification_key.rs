use crate::{
    constants::{RING_ELEMENT_OF_T1S_SIZE, SEED_FOR_A_SIZE},
    encoding::t1,
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn generate_serialized<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const VERIFICATION_KEY_SIZE: usize,
>(
    seed_for_A: &[u8],
    t1: [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
) -> [u8; VERIFICATION_KEY_SIZE] {
    let mut verification_key_serialized = [0u8; VERIFICATION_KEY_SIZE];
    verification_key_serialized[0..SEED_FOR_A_SIZE].copy_from_slice(seed_for_A);

    for (i, ring_element) in t1.iter().enumerate() {
        let offset = SEED_FOR_A_SIZE + (i * RING_ELEMENT_OF_T1S_SIZE);
        verification_key_serialized[offset..offset + RING_ELEMENT_OF_T1S_SIZE]
            .copy_from_slice(&t1::serialize::<SIMDUnit>(*ring_element));
    }

    verification_key_serialized
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn deserialize<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const VERIFICATION_KEY_SIZE: usize,
>(
    serialized: &[u8; VERIFICATION_KEY_SIZE],
) -> (
    [u8; SEED_FOR_A_SIZE],
    [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
) {
    let mut t1 = [PolynomialRingElement::<SIMDUnit>::ZERO(); ROWS_IN_A];
    let (seed_for_A, serialized_remaining) = serialized.split_at(SEED_FOR_A_SIZE);

    for i in 0..ROWS_IN_A {
        t1[i] = t1::deserialize::<SIMDUnit>(
            &serialized_remaining[i * RING_ELEMENT_OF_T1S_SIZE..(i + 1) * RING_ELEMENT_OF_T1S_SIZE],
        );
    }

    (seed_for_A.try_into().unwrap(), t1)
}
