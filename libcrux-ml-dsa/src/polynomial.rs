use crate::{
    arithmetic::FieldElement,
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS},
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct PolynomialRingElement {
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
