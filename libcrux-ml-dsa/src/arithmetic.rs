use crate::{
    constants::COEFFICIENTS_IN_RING_ELEMENT,
    polynomial::{PolynomialRingElement, SIMDPolynomialRingElement, SIMD_UNITS_IN_RING_ELEMENT},
    simd::{portable::PortableSIMDUnit, traits::Operations},
};

#[inline(always)]
pub(crate) fn vector_infinity_norm_exceeds<const DIMENSION: usize>(
    vector: [PolynomialRingElement; DIMENSION],
    bound: i32,
) -> bool {
    let mut exceeds = false;

    // TODO: We can break out of this loop early if need be, but the most
    // straightforward way to do so (returning false) will not go through hax;
    // revisit if performance is impacted.
    for ring_element in vector.iter() {
        let simd_re = SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(
            *ring_element,
        );
        exceeds |= simd_re.infinity_norm_exceeds(bound);
    }

    exceeds
}

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub(crate) type FieldElementTimesMontgomeryR = i32;

#[inline(always)]
pub(crate) fn shift_left_then_reduce(
    re: PolynomialRingElement,
    shift_by: usize,
) -> PolynomialRingElement {
    let v_re = SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(re);
    let mut out = SIMDPolynomialRingElement::ZERO();

    for (i, simd_unit) in v_re.simd_units.iter().enumerate() {
        out.simd_units[i] = PortableSIMDUnit::shift_left_then_reduce(*simd_unit, shift_by);
    }

    out.to_polynomial_ring_element()
}

#[inline(always)]
pub(crate) fn power2round_vector<SIMDUnit: Operations, const DIMENSION: usize>(
    t: [SIMDPolynomialRingElement<SIMDUnit>; DIMENSION],
) -> (
    [SIMDPolynomialRingElement<SIMDUnit>; DIMENSION],
    [SIMDPolynomialRingElement<SIMDUnit>; DIMENSION],
) {
    let mut t0 = [SIMDPolynomialRingElement::<SIMDUnit>::ZERO(); DIMENSION];
    let mut t1 = [SIMDPolynomialRingElement::<SIMDUnit>::ZERO(); DIMENSION];

    for (i, ring_element) in t.iter().enumerate() {
        for (j, simd_unit) in ring_element.simd_units.iter().enumerate() {
            let (t0_unit, t1_unit) = SIMDUnit::power2round(*simd_unit);

            t0[i].simd_units[j] = t0_unit;
            t1[i].simd_units[j] = t1_unit;
        }
    }

    (t0, t1)
}

#[inline(always)]
pub(crate) fn decompose_vector<const DIMENSION: usize, const GAMMA2: i32>(
    t: [PolynomialRingElement; DIMENSION],
) -> (
    [PolynomialRingElement; DIMENSION],
    [PolynomialRingElement; DIMENSION],
) {
    let mut vector_low = [PolynomialRingElement::ZERO; DIMENSION];
    let mut vector_high = [PolynomialRingElement::ZERO; DIMENSION];

    for i in 0..DIMENSION {
        let v_t = SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(t[i]);

        let mut v_low = SIMDPolynomialRingElement::ZERO();
        let mut v_high = SIMDPolynomialRingElement::ZERO();

        for j in 0..v_low.simd_units.len() {
            let (low, high) = PortableSIMDUnit::decompose::<GAMMA2>(v_t.simd_units[j]);

            v_low.simd_units[j] = low;
            v_high.simd_units[j] = high;
        }

        vector_low[i] = v_low.to_polynomial_ring_element();
        vector_high[i] = v_high.to_polynomial_ring_element();
    }

    (vector_low, vector_high)
}

#[inline(always)]
pub(crate) fn make_hint<const DIMENSION: usize, const GAMMA2: i32>(
    low: [PolynomialRingElement; DIMENSION],
    high: [PolynomialRingElement; DIMENSION],
) -> ([[i32; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION], usize) {
    let mut hint = [[0; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION];
    let mut true_hints = 0;

    for i in 0..DIMENSION {
        let v_low =
            SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(low[i]);
        let v_high =
            SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(high[i]);

        let mut v_hint = SIMDPolynomialRingElement::ZERO();

        for j in 0..v_hint.simd_units.len() {
            let (one_hints_count, current_hint) =
                PortableSIMDUnit::compute_hint::<GAMMA2>(v_low.simd_units[j], v_high.simd_units[j]);
            v_hint.simd_units[j] = current_hint;

            true_hints += one_hints_count;
        }

        hint[i] = v_hint.to_polynomial_ring_element().coefficients;
    }

    (hint, true_hints)
}

#[inline(always)]
pub(crate) fn use_hint<const DIMENSION: usize, const GAMMA2: i32>(
    hint: [[i32; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION],
    re_vector: [PolynomialRingElement; DIMENSION],
) -> [PolynomialRingElement; DIMENSION] {
    let mut result = [PolynomialRingElement::ZERO; DIMENSION];

    for i in 0..DIMENSION {
        let v_re = SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(
            re_vector[i],
        );
        let v_hint = SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(
            PolynomialRingElement {
                coefficients: hint[i],
            },
        );

        let mut res = SIMDPolynomialRingElement::ZERO();
        for j in 0..SIMD_UNITS_IN_RING_ELEMENT {
            res.simd_units[j] =
                PortableSIMDUnit::use_hint::<GAMMA2>(v_re.simd_units[j], v_hint.simd_units[j]);
        }

        result[i] = res.to_polynomial_ring_element();
    }

    result
}
