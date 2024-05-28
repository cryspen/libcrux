use crate::constants::{BITS_IN_LOWER_PART_OF_T, COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

#[derive(Clone, Copy)]
pub struct PolynomialRingElement {
    pub(crate) coefficients: [FieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl PolynomialRingElement {
    pub const ZERO: Self = Self {
        // FIXME: hax issue, 256 is COEFFICIENTS_IN_RING_ELEMENT
        coefficients: [0i32; 256],
    };
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

// Splits 0 ≤ t < Q into t0 and t1 with a = t1*2ᴰ + t0
// and -2ᴰ⁻¹ < t0 < 2ᴰ⁻¹.  Returns t0 and t1 computed as.
//
// - t0 = t mod± 2ᵈ
// - t1 = (t - t0) / 2ᵈ.
//
// This approach has been taken from:
// https://github.com/cloudflare/circl/blob/main/sign/dilithium/internal/common/field.go#L35
pub(crate) fn power2round(t: i32) -> (i32, i32) {
    debug_assert!(t >= 0 && t < FIELD_MODULUS);

    // Compute t mod 2ᵈ
    // t0 is now one of 0, 1, ..., 2ᵈ⁻¹-1, 2ᵈ⁻¹, 2ᵈ⁻¹+1, ..., 2ᵈ-1
    let mut t0 = t & ((1 << BITS_IN_LOWER_PART_OF_T) - 1);

    // now t0 is -2ᵈ⁻¹-1, -2ᵈ⁻¹, ..., -2, -1, 0, ..., 2ᵈ⁻¹-2
    t0 -= (1 << (BITS_IN_LOWER_PART_OF_T - 1)) + 1;

    // Next, we add 2ᴰ to those t0 that are negative
    // now a0 is 2ᵈ⁻¹-1, 2ᵈ⁻¹, ..., 2ᵈ-2, 2ᵈ-1, 0, ..., 2ᵈ⁻¹-2
    t0 += (t0 >> 31) & (1 << BITS_IN_LOWER_PART_OF_T);

    // now t0 is 0, 1, 2, ..., 2ᵈ⁻¹-1, 2ᵈ⁻¹-1, -2ᵈ⁻¹-1, ...
    // which is what we want.
    t0 -= (1 << (BITS_IN_LOWER_PART_OF_T - 1)) - 1;

    let t1 = (t - t0) >> BITS_IN_LOWER_PART_OF_T;

    (t0, t1)
}

pub(crate) fn t0_to_unsigned_representative(t0: i32) -> i32 {
    (1 << (BITS_IN_LOWER_PART_OF_T - 1)) - t0
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
        assert_eq!(power2round(2898283), (-1685, 354));
        assert_eq!(power2round(3821421), (3949, 466));
        assert_eq!(power2round(2577417), (-3063, 315));
    }
}
