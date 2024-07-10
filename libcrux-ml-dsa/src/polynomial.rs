use crate::{
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS},
    vector::traits::{Operations, COEFFICIENTS_PER_VECTOR},
};

pub(crate) const VECTORS_IN_RING_ELEMENT: usize =
    super::constants::COEFFICIENTS_IN_RING_ELEMENT / COEFFICIENTS_PER_VECTOR;

#[derive(Clone, Copy)]
pub(crate) struct PolynomialRingElement {
    pub(crate) coefficients: [i32; COEFFICIENTS_IN_RING_ELEMENT],
}

impl PolynomialRingElement {
    pub const ZERO: Self = Self {
        coefficients: [0; COEFFICIENTS_IN_RING_ELEMENT],
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

#[derive(Clone, Copy)]
pub(crate) struct VectorPolynomialRingElement<Vector: Operations> {
    pub(crate) coefficients: [Vector; VECTORS_IN_RING_ELEMENT],
}
impl<Vector: Operations> VectorPolynomialRingElement<Vector> {
    #[allow(non_snake_case)]
    pub(crate) fn ZERO() -> Self {
        Self {
            coefficients: [Vector::ZERO(); VECTORS_IN_RING_ELEMENT],
        }
    }

    pub(crate) fn to_polynomial_ring_element(&self) -> PolynomialRingElement {
        let mut counter = 0;
        let mut out = PolynomialRingElement::ZERO;

        for coefficient_vector in self.coefficients {
            for coefficient in Vector::to_i32_array(coefficient_vector) {
                out.coefficients[counter] = coefficient;
                counter += 1;
            }
        }

        out
    }

    pub(crate) fn from_polynomial_ring_element(re: PolynomialRingElement) -> Self {
        let mut out = Self::ZERO();

        for (i, coefficients) in re.coefficients.chunks(COEFFICIENTS_PER_VECTOR).enumerate() {
            out.coefficients[i] = Vector::from_i32_array(coefficients);
        }

        out
    }

    #[inline(always)]
    pub(crate) fn add(&self, rhs: &Self) -> Self {
        let mut sum = Self::ZERO();

        for i in 0..sum.coefficients.len() {
            sum.coefficients[i] = Vector::add(&self.coefficients[i], &rhs.coefficients[i]);
        }

        sum
    }

    #[inline(always)]
    pub(crate) fn subtract(&self, rhs: &Self) -> Self {
        let mut difference = Self::ZERO();

        for i in 0..difference.coefficients.len() {
            difference.coefficients[i] =
                Vector::subtract(&self.coefficients[i], &rhs.coefficients[i]);
        }

        difference
    }
}
