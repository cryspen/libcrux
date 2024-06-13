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
}

pub(crate) fn add_to_ring_element(
    mut lhs: PolynomialRingElement,
    rhs: &PolynomialRingElement,
) -> PolynomialRingElement {
    for i in 0..lhs.coefficients.len() {
        lhs.coefficients[i] += rhs.coefficients[i];
    }

    lhs
}

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

// Splits t ∈ {0, ..., q-1} into t0 and t1 with a = t1*2ᴰ + t0
// and -2ᴰ⁻¹ < t0 < 2ᴰ⁻¹.  Returns t0 and t1 computed as.
//
// - t0 = t mod± 2ᵈ
// - t1 = (t - t0) / 2ᵈ.
//
// We assume the input t is in the signed representative range and convert it
// to the standard unsigned range.
pub(crate) fn power2round(t: i32) -> (i32, i32) {
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

pub(crate) fn t0_to_unsigned_representative(t0: i32) -> i32 {
    (1 << (BITS_IN_LOWER_PART_OF_T - 1)) - t0
}

// Splits 0 ≤ r < q into r₀ and r₁ such that:
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
pub(crate) fn decompose<const ALPHA: i32>(r: i32) -> (i32, i32) {
    let r1 = {
        // Compute ⌈r / 128⌉
        let ceil_of_r_by_128 = (r + 127) >> 7;

        match ALPHA {
            190_464 => {
                // 1488/2²⁴ is an approximation of 1/1488
                let result = ((ceil_of_r_by_128 * 11_275) + (1 << 23)) >> 24;

                // For the corner-case a₁ = (q-1)/α = 44, we have to set a₁=0.
                (result ^ (43 - result) >> 31) & result
            }
            523_776 => {
                // 1025/2²² is an approximation of 1/4092
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

pub(crate) fn make_hint<const GAMMA2: i32>(low: i32, high: i32) -> bool {
    (low > GAMMA2) || (low < -GAMMA2) || (low == -GAMMA2 && high != 0)
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
        assert_eq!(decompose::<190_464>(3574899), (-43917, 19));
        assert_eq!(decompose::<190_464>(7368323), (-59773, 39));
        assert_eq!(decompose::<190_464>(3640854), (22038, 19));

        assert_eq!(decompose::<523_776>(563751), (39975, 1));
        assert_eq!(decompose::<523_776>(6645076), (-164012, 13));
        assert_eq!(decompose::<523_776>(7806985), (-49655, 15));
    }
}
