use crate::{
    constants::COEFFICIENTS_IN_RING_ELEMENT, helper::cloop, polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[inline(always)]
pub(crate) fn vector_infinity_norm_exceeds<SIMDUnit: Operations, const DIMENSION: usize>(
    vector: [PolynomialRingElement<SIMDUnit>; DIMENSION],
    bound: i32,
) -> bool {
    let mut exceeds = false;

    // TODO: We can break out of this loop early if need be, but the most
    // straightforward way to do so (returning false) will not go through hax;
    // revisit if performance is impacted.
    cloop! {
        for ring_element in vector.iter() {
            exceeds = exceeds || ring_element.infinity_norm_exceeds(bound);
        }
    }

    exceeds
}

#[inline(always)]
pub(crate) fn shift_left_then_reduce<SIMDUnit: Operations, const SHIFT_BY: i32>(
    re: &mut PolynomialRingElement<SIMDUnit>,
) {
    for i in 0..re.simd_units.len() {
        SIMDUnit::shift_left_then_reduce::<SHIFT_BY>(&mut re.simd_units[i]);
    }
}

#[inline(always)]
pub(crate) fn power2round_vector<SIMDUnit: Operations, const DIMENSION: usize>(
    t: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
    t1: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
) {
    for i in 0..t.len() {
        for j in 0..t[i].simd_units.len() {
            SIMDUnit::power2round(&mut t[i].simd_units[j], &mut t1[i].simd_units[j]);
        }
    }
}

#[inline(always)]
pub(crate) fn decompose_vector<SIMDUnit: Operations, const DIMENSION: usize, const GAMMA2: i32>(
    t: [PolynomialRingElement<SIMDUnit>; DIMENSION],
    low: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
    high: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
) {
    for i in 0..DIMENSION {
        for j in 0..low[0].simd_units.len() {
            SIMDUnit::decompose::<GAMMA2>(
                &t[i].simd_units[j],
                &mut low[i].simd_units[j],
                &mut high[i].simd_units[j],
            );
        }
    }
}

#[inline(always)]
pub(crate) fn make_hint<SIMDUnit: Operations, const DIMENSION: usize, const GAMMA2: i32>(
    low: [PolynomialRingElement<SIMDUnit>; DIMENSION],
    high: [PolynomialRingElement<SIMDUnit>; DIMENSION],
) -> ([[i32; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION], usize) {
    let mut hint = [[0; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION];
    let mut true_hints = 0;

    for i in 0..DIMENSION {
        let mut hint_simd = PolynomialRingElement::<SIMDUnit>::ZERO();

        for j in 0..hint_simd.simd_units.len() {
            let (one_hints_count, current_hint) =
                SIMDUnit::compute_hint::<GAMMA2>(&low[i].simd_units[j], &high[i].simd_units[j]);
            hint_simd.simd_units[j] = current_hint;

            true_hints += one_hints_count;
        }

        hint[i] = hint_simd.to_i32_array();
    }

    (hint, true_hints)
}

#[inline(always)]
pub(crate) fn use_hint<SIMDUnit: Operations, const DIMENSION: usize, const GAMMA2: i32>(
    hint: [[i32; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION],
    re_vector: [PolynomialRingElement<SIMDUnit>; DIMENSION],
) -> [PolynomialRingElement<SIMDUnit>; DIMENSION] {
    let mut result = [PolynomialRingElement::<SIMDUnit>::ZERO(); DIMENSION];

    for i in 0..DIMENSION {
        // XXX: Why can't we keep the hint as simd units?
        PolynomialRingElement::<SIMDUnit>::from_i32_array(&hint[i], &mut result[i]);

        for j in 0..result[0].simd_units.len() {
            SIMDUnit::use_hint::<GAMMA2>(&re_vector[i].simd_units[j], &mut result[i].simd_units[j]);
        }
    }

    result
}
