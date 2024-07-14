use crate::{
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS},
    polynomial::{PolynomialRingElement, SIMDPolynomialRingElement},
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
pub(crate) fn power2round_vector<const DIMENSION: usize>(
    vector_t: [PolynomialRingElement; DIMENSION],
) -> (
    [PolynomialRingElement; DIMENSION],
    [PolynomialRingElement; DIMENSION],
) {
    let mut vector_t0 = [PolynomialRingElement::ZERO; DIMENSION];
    let mut vector_t1 = [PolynomialRingElement::ZERO; DIMENSION];

    for (i, ring_element) in vector_t.iter().enumerate() {
        // These conversions are rather unsightly, but are very temporary and
        // will be removed once the entire codebase is switched to use
        // SIMDPolynomialRingElement
        let mut t0_simd_ring_element = SIMDPolynomialRingElement::ZERO();
        let mut t1_simd_ring_element = SIMDPolynomialRingElement::ZERO();

        for (j, simd_unit) in SIMDPolynomialRingElement::from_polynomial_ring_element(*ring_element)
            .simd_units
            .iter()
            .enumerate()
        {
            let (t0_simd_unit, t1_simd_unit) = PortableSIMDUnit::power2round(*simd_unit);

            t0_simd_ring_element.simd_units[j] = t0_simd_unit;
            t1_simd_ring_element.simd_units[j] = t1_simd_unit;
        }

        vector_t0[i] = t0_simd_ring_element.to_polynomial_ring_element();
        vector_t1[i] = t1_simd_ring_element.to_polynomial_ring_element();
    }

    (vector_t0, vector_t1)
}

// Take a representative -q < r < q and convert it
// to the standard unsigned one in the interval [0, q).
//
// Splits this representative r into r₀ and r₁ such that:
//
// - r = r₁*α + r₀
// - -α/2 < r₀ ≤ α/2
//
// except when r₁ = (q-1)/α; in this case:
//
// - r₁ is set to 0 is taken
// - α/2 ≤ r₀ < 0.
//
// Note that 0 ≤ r₁ < (q-1)/α.
#[allow(non_snake_case)]
#[inline(always)]
fn decompose<const GAMMA2: i32>(r: i32) -> (i32, i32) {
    debug_assert!(
        r > -FIELD_MODULUS && r < FIELD_MODULUS,
        "the representative is {}",
        r
    );

    // Convert the signed representative to the standard unsigned one.
    let r = r + ((r >> 31) & FIELD_MODULUS);

    let ALPHA = GAMMA2 * 2;

    let r1 = {
        // Compute ⌈r / 128⌉
        let ceil_of_r_by_128 = (r + 127) >> 7;

        match ALPHA {
            190_464 => {
                // We approximate 1 / 1488 as:
                // ⌊2²⁴ / 1488⌋ / 2²⁴ = 11,275 / 2²⁴
                let result = ((ceil_of_r_by_128 * 11_275) + (1 << 23)) >> 24;

                // For the corner-case a₁ = (q-1)/α = 44, we have to set a₁=0.
                (result ^ (43 - result) >> 31) & result
            }
            523_776 => {
                // We approximate 1 / 4092 as:
                // ⌊2²² / 4092⌋ / 2²² = 1025 / 2²²
                let result = (ceil_of_r_by_128 * 1025 + (1 << 21)) >> 22;

                // For the corner-case a₁ = (q-1)/α = 16, we have to set a₁=0.
                result & 15
            }
            _ => unreachable!(),
        }
    };

    let mut r0 = r - (r1 * ALPHA);

    // In the corner-case, when we set a₁=0, we will incorrectly
    // have a₀ > (q-1)/2 and we'll need to subtract q.  As we
    // return a₀ + q, that comes down to adding q if a₀ < (q-1)/2.
    r0 -= (((FIELD_MODULUS - 1) / 2 - r0) >> 31) & FIELD_MODULUS;

    (r0, r1)
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
        for (j, coefficient) in t[i].coefficients.into_iter().enumerate() {
            let (low, high) = decompose::<GAMMA2>(coefficient);

            vector_low[i].coefficients[j] = low;
            vector_high[i].coefficients[j] = high;
        }
    }

    (vector_low, vector_high)
}

#[inline(always)]
fn compute_hint_value<const GAMMA2: i32>(low: i32, high: i32) -> i32 {
    if (low > GAMMA2) || (low < -GAMMA2) || (low == -GAMMA2 && high != 0) {
        1
    } else {
        0
    }
}

#[inline(always)]
pub(crate) fn make_hint<const DIMENSION: usize, const GAMMA2: i32>(
    low: [PolynomialRingElement; DIMENSION],
    high: [PolynomialRingElement; DIMENSION],
) -> ([[i32; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION], usize) {
    let mut hint = [[0; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION];
    let mut true_hints = 0;

    for i in 0..DIMENSION {
        for j in 0..COEFFICIENTS_IN_RING_ELEMENT {
            hint[i][j] =
                compute_hint_value::<GAMMA2>(low[i].coefficients[j], high[i].coefficients[j]);

            // From https://doc.rust-lang.org/std/primitive.bool.html:
            // "If you cast a bool into an integer, true will be 1 and false will be 0."
            true_hints += hint[i][j] as usize;
        }
    }

    (hint, true_hints)
}

#[inline(always)]
pub(crate) fn use_hint_value<const GAMMA2: i32>(r: i32, hint: i32) -> i32 {
    let (r0, r1) = decompose::<GAMMA2>(r);

    if hint == 0 {
        return r1;
    }

    match GAMMA2 {
        95_232 => {
            if r0 > 0 {
                if r1 == 43 {
                    0
                } else {
                    r1 + 1
                }
            } else if r1 == 0 {
                43
            } else {
                r1 - 1
            }
        }

        261_888 => {
            if r0 > 0 {
                (r1 + 1) & 15
            } else {
                (r1 - 1) & 15
            }
        }

        _ => unreachable!(),
    }
}

#[inline(always)]
pub(crate) fn use_hint<const DIMENSION: usize, const GAMMA2: i32>(
    hint: [[i32; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION],
    re_vector: [PolynomialRingElement; DIMENSION],
) -> [PolynomialRingElement; DIMENSION] {
    let mut result = [PolynomialRingElement::ZERO; DIMENSION];

    for i in 0..DIMENSION {
        for j in 0..COEFFICIENTS_IN_RING_ELEMENT {
            result[i].coefficients[j] =
                use_hint_value::<GAMMA2>(re_vector[i].coefficients[j], hint[i][j]);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decompose() {
        assert_eq!(decompose::<95_232>(3574899), (-43917, 19));
        assert_eq!(decompose::<95_232>(7368323), (-59773, 39));
        assert_eq!(decompose::<95_232>(3640854), (22038, 19));

        assert_eq!(decompose::<261_888>(563751), (39975, 1));
        assert_eq!(decompose::<261_888>(6645076), (-164012, 13));
        assert_eq!(decompose::<261_888>(7806985), (-49655, 15));
    }

    #[test]
    fn test_use_hint_value() {
        assert_eq!(use_hint_value::<95_232>(7622170, 0), 40);
        assert_eq!(use_hint_value::<95_232>(2332762, 1), 13);

        assert_eq!(use_hint_value::<261_888>(7691572, 0), 15);
        assert_eq!(use_hint_value::<261_888>(6635697, 1), 12);
    }
}
