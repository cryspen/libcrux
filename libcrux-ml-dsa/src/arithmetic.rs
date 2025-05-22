use crate::{
    constants::{Gamma2, COEFFICIENTS_IN_RING_ELEMENT},
    helper::cloop,
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[inline(always)]
pub(crate) fn vector_infinity_norm_exceeds<SIMDUnit: Operations>(
    vector: &[PolynomialRingElement<SIMDUnit>],
    bound: i32,
) -> bool {
    let mut result = false;
    cloop! {
        for ring_element in vector.iter() {
            result = result || ring_element.infinity_norm_exceeds(bound);
        }
    }

    result
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
pub(crate) fn power2round_vector<SIMDUnit: Operations>(
    t: &mut [PolynomialRingElement<SIMDUnit>],
    t1: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..t.len() {
        for j in 0..t[i].simd_units.len() {
            SIMDUnit::power2round(&mut t[i].simd_units[j], &mut t1[i].simd_units[j]);
        }
    }
}

#[inline(always)]
#[hax_lib::requires(t.len() == dimension && low.len() == dimension && high.len() == dimension)]
pub(crate) fn decompose_vector<SIMDUnit: Operations>(
    dimension: usize,
    gamma2: Gamma2,
    t: &[PolynomialRingElement<SIMDUnit>],
    low: &mut [PolynomialRingElement<SIMDUnit>],
    high: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..dimension {
        hax_lib::loop_invariant!(|i: usize| low.len() == dimension && high.len() == dimension);

        for j in 0..low[0].simd_units.len() {
            hax_lib::loop_invariant!(|i: usize| low.len() == dimension && high.len() == dimension);

            SIMDUnit::decompose(
                gamma2,
                &t[i].simd_units[j],
                &mut low[i].simd_units[j],
                &mut high[i].simd_units[j],
            );
        }
    }
}

#[inline(always)]
#[hax_lib::requires(low.len() == high.len() && hint.len() == low.len() && low.len() <= 8)]
pub(crate) fn make_hint<SIMDUnit: Operations>(
    low: &[PolynomialRingElement<SIMDUnit>],
    high: &[PolynomialRingElement<SIMDUnit>],
    gamma2: i32,
    hint: &mut [[i32; COEFFICIENTS_IN_RING_ELEMENT]],
) -> usize {
    let mut true_hints = 0;
    let mut hint_simd = PolynomialRingElement::<SIMDUnit>::zero();

    for i in 0..low.len() {
        hax_lib::loop_invariant!(|i: usize| true_hints <= 256 * i && hint.len() == low.len());

        for j in 0..hint_simd.simd_units.len() {
            hax_lib::loop_invariant!(|j: usize| true_hints <= 256 * i + 8 * j);

            let one_hints_count = SIMDUnit::compute_hint(
                &low[i].simd_units[j],
                &high[i].simd_units[j],
                gamma2,
                &mut hint_simd.simd_units[j],
            );

            true_hints += one_hints_count;
        }

        hint[i] = hint_simd.to_i32_array();
    }

    true_hints
}

#[inline(always)]
#[hax_lib::requires(hint.len() == re_vector.len() && hint.len() <= 8)]
pub(crate) fn use_hint<SIMDUnit: Operations>(
    gamma2: Gamma2,
    hint: &[[i32; COEFFICIENTS_IN_RING_ELEMENT]],
    re_vector: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..re_vector.len() {
        hax_lib::loop_invariant!(|j: usize| re_vector.len() == hint.len());

        let mut tmp = PolynomialRingElement::zero();
        PolynomialRingElement::<SIMDUnit>::from_i32_array(&hint[i], &mut tmp);

        for j in 0..re_vector[0].simd_units.len() {
            SIMDUnit::use_hint(gamma2, &re_vector[i].simd_units[j], &mut tmp.simd_units[j]);
        }
        re_vector[i] = tmp;
    }
}
