use crate::constants::{BITS_IN_LOWER_PART_OF_T, COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

/// Values having this type hold a representative 'x' of the ML-DSA field.
pub(crate) type FieldElement = i32;

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
    fn test_power2round() {
        assert_eq!(power2round(2898283), (-1685, 354));
        assert_eq!(power2round(3821421), (3949, 466));
        assert_eq!(power2round(2577417), (-3063, 315));
    }
}
