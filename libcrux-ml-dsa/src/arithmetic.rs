use crate::constants::{BITS_IN_LOWER_PART_OF_T, COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

#[derive(Clone, Copy, Debug)]
pub struct PolynomialRingElement {
    pub(crate) coefficients: [FieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl PolynomialRingElement {
    pub const ZERO: Self = Self {
        // FIXME: hax issue, 256 is COEFFICIENTS_IN_RING_ELEMENT
        coefficients: [0i32; 256],
    };

    #[inline(always)]
    pub(crate) fn add(&self, rhs: &Self) -> Self {
        let mut sum = Self::ZERO;

        for i in 0..rhs.coefficients.len() {
            sum.coefficients[i] = self.coefficients[i] + rhs.coefficients[i];
        }

        sum
    }

    #[inline(always)]
    pub(crate) fn sub(&self, rhs: &Self) -> Self {
        let mut difference = Self::ZERO;

        for i in 0..rhs.coefficients.len() {
            difference.coefficients[i] = self.coefficients[i] - rhs.coefficients[i];
        }

        difference
    }

    // TODO: Revisit this function when doing the range analysis and testing
    // additional KATs.
    #[inline(always)]
    pub(crate) fn infinity_norm_exceeds(&self, bound: i32) -> bool {
        let mut exceeds = false;

        // It is ok to leak which coefficient violates the bound since
        // the probability for each coefficient is independent of secret
        // data but we must not leak the sign of the centralized representative.
        //
        // TODO: We can break out of this loop early if need be, but the most
        // straightforward way to do so (returning false) will not go through hax;
        // revisit if performance is impacted.
        for coefficient in self.coefficients.into_iter() {
            debug_assert!(
                coefficient > -FIELD_MODULUS && coefficient < FIELD_MODULUS,
                "coefficient is {}",
                coefficient
            );
            // This norm is calculated using the absolute value of the
            // signed representative in the range:
            //
            // -FIELD_MODULUS / 2 < r <= FIELD_MODULUS / 2.
            //
            // So if the coefficient is negative, get its absolute value, but
            // don't convert it into a different representation.
            let sign = coefficient >> 31;
            let normalized = coefficient - (sign & (2 * coefficient));

            exceeds |= normalized >= bound;
        }

        exceeds
    }
}

#[inline(always)]
pub(crate) fn vector_infinity_norm_exceeds<const DIMENSION: usize>(
    vector: [PolynomialRingElement; DIMENSION],
    value: i32,
) -> bool {
    let mut exceeds = false;

    // TODO: We can break out of this loop early if need be, but the most
    // straightforward way to do so (returning false) will not go through hax;
    // revisit if performance is impacted.
    for ring_element in vector.iter() {
        exceeds |= ring_element.infinity_norm_exceeds(value);
    }

    exceeds
}

#[inline(always)]
pub(crate) fn get_n_least_significant_bits(n: u8, value: u64) -> u64 {
    value & ((1 << n) - 1)
}

/// Values having this type hold a representative 'x' of the ML-DSA field.
pub(crate) type FieldElement = i32;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R^(-1) (mod FIELD_MODULUS).
/// We use 'mfe' as a shorthand for this type
pub(crate) type MontgomeryFieldElement = i32;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub(crate) type FieldElementTimesMontgomeryR = i32;

const MONTGOMERY_SHIFT: u8 = 32;
const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58_728_449; // FIELD_MODULUS^{-1} mod 2^32

#[inline(always)]
pub(crate) fn montgomery_reduce(value: i64) -> MontgomeryFieldElement {
    let t = get_n_least_significant_bits(MONTGOMERY_SHIFT, value as u64)
        * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    let k = get_n_least_significant_bits(MONTGOMERY_SHIFT, t) as i32;

    let k_times_modulus = (k as i64) * (FIELD_MODULUS as i64);

    let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i32;
    let value_high = (value >> MONTGOMERY_SHIFT) as i32;

    value_high - c
}

#[inline(always)]
pub(crate) fn montgomery_multiply_fe_by_fer(
    fe: FieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> FieldElement {
    montgomery_reduce((fe as i64) * (fer as i64))
}

fn reduce(fe: FieldElement) -> FieldElement {
    let quotient = (fe + (1 << 22)) >> 23;

    fe - (quotient * FIELD_MODULUS)
}

pub(crate) fn shift_coefficients_left_then_reduce(
    re: PolynomialRingElement,
    shift_by: usize,
) -> PolynomialRingElement {
    let mut out = PolynomialRingElement::ZERO;

    for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
        out.coefficients[i] = reduce(re.coefficients[i] << shift_by);
    }

    out
}

// Splits t ∈ {0, ..., q-1} into t0 and t1 with a = t1*2ᴰ + t0
// and -2ᴰ⁻¹ < t0 < 2ᴰ⁻¹.  Returns t0 and t1 computed as.
//
// - t0 = t mod± 2ᵈ
// - t1 = (t - t0) / 2ᵈ.
//
// We assume the input t is in the signed representative range and convert it
// to the standard unsigned range.
#[inline(always)]
fn power2round(t: i32) -> (i32, i32) {
    debug_assert!(t > -FIELD_MODULUS && t < FIELD_MODULUS, "t is {}", t);

    // Convert the signed representative to the standard unsigned one.
    let t = t + ((t >> 31) & FIELD_MODULUS);

    // t0 = t - (2^{BITS_IN_LOWER_PART_OF_T} * t1)
    // t1 = ⌊(t - 1)/2^{BITS_IN_LOWER_PART_OF_T} + 1/2⌋
    //
    // See Lemma 10 of the implementation notes document for more information
    // on what these compute.
    let t1 = (t - 1 + (1 << (BITS_IN_LOWER_PART_OF_T - 1))) >> BITS_IN_LOWER_PART_OF_T;
    let t0 = t - (t1 << BITS_IN_LOWER_PART_OF_T);

    (t0, t1)
}

#[inline(always)]
pub(crate) fn power2round_vector<const DIMENSION: usize>(
    t: [PolynomialRingElement; DIMENSION],
) -> (
    [PolynomialRingElement; DIMENSION],
    [PolynomialRingElement; DIMENSION],
) {
    let mut vector_t0 = [PolynomialRingElement::ZERO; DIMENSION];
    let mut vector_t1 = [PolynomialRingElement::ZERO; DIMENSION];

    for i in 0..DIMENSION {
        for (j, coefficient) in t[i].coefficients.into_iter().enumerate() {
            let (c0, c1) = power2round(coefficient);

            vector_t0[i].coefficients[j] = c0;
            vector_t1[i].coefficients[j] = c1;
        }
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
fn compute_hint_value<const GAMMA2: i32>(low: i32, high: i32) -> bool {
    (low > GAMMA2) || (low < -GAMMA2) || (low == -GAMMA2 && high != 0)
}

#[inline(always)]
pub(crate) fn make_hint<const DIMENSION: usize, const GAMMA2: i32>(
    low: [PolynomialRingElement; DIMENSION],
    high: [PolynomialRingElement; DIMENSION],
) -> ([[bool; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION], usize) {
    let mut hint = [[false; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION];
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
pub(crate) fn use_hint_value<const GAMMA2: i32>(r: i32, hint: bool) -> i32 {
    let (r0, r1) = decompose::<GAMMA2>(r);

    if !hint {
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
    hint: [[bool; COEFFICIENTS_IN_RING_ELEMENT]; DIMENSION],
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
    fn test_montgomery_reduce() {
        assert_eq!(montgomery_reduce(10933346042510), -1553279);
        assert_eq!(montgomery_reduce(-20392060523118), 1331779);
        assert_eq!(montgomery_reduce(13704140696092), -1231016);
        assert_eq!(montgomery_reduce(-631922212176), -2580954);
    }

    #[test]
    fn test_power2round() {
        assert_eq!(power2round(669975), (-1769, 82));
        assert_eq!(power2round(1843331), (131, 225));
        assert_eq!(power2round(-1568816), (4049, 831));
        assert_eq!(power2round(-4022142), (131, 532));
    }

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
        assert_eq!(use_hint_value::<95_232>(7622170, false), 40);
        assert_eq!(use_hint_value::<95_232>(2332762, true), 13);

        assert_eq!(use_hint_value::<261_888>(7691572, false), 15);
        assert_eq!(use_hint_value::<261_888>(6635697, true), 12);
    }
}
