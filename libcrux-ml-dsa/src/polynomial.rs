use crate::{
    constants::COEFFICIENTS_IN_RING_ELEMENT,
    simd::traits::{Operations, COEFFICIENTS_IN_SIMD_UNIT},
};

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
}

pub(crate) const SIMD_UNITS_IN_RING_ELEMENT: usize =
    crate::constants::COEFFICIENTS_IN_RING_ELEMENT / COEFFICIENTS_IN_SIMD_UNIT;

#[derive(Clone, Copy)]
pub(crate) struct SIMDPolynomialRingElement<SIMDUnit: Operations> {
    pub(crate) simd_units: [SIMDUnit; SIMD_UNITS_IN_RING_ELEMENT],
}
impl<SIMDUnit: Operations> SIMDPolynomialRingElement<SIMDUnit> {
    #[allow(non_snake_case)]
    pub(crate) fn ZERO() -> Self {
        Self {
            simd_units: [SIMDUnit::ZERO(); SIMD_UNITS_IN_RING_ELEMENT],
        }
    }

    // This is useful for debugging.
    #[allow(dead_code)]
    pub(crate) fn from_i32_array(array: &[i32]) -> Self {
        debug_assert!(array.len() == 256);

        let mut array_chunks = array.chunks(COEFFICIENTS_IN_SIMD_UNIT);

        let mut result = Self::ZERO();

        for i in 0..SIMD_UNITS_IN_RING_ELEMENT {
            result.simd_units[i] = SIMDUnit::from_i32_array(&array_chunks.next().unwrap());
        }
        result
    }

    pub(crate) fn infinity_norm_exceeds(&self, bound: i32) -> bool {
        let mut exceeds = false;

        for simd_unit in self.simd_units {
            exceeds |= SIMDUnit::infinity_norm_exceeds(simd_unit, bound);
        }

        exceeds
    }

    pub(crate) fn to_polynomial_ring_element(&self) -> PolynomialRingElement {
        let mut counter = 0;
        let mut out = PolynomialRingElement::ZERO;

        for unit in self.simd_units {
            for coefficient in SIMDUnit::to_i32_array(unit) {
                out.coefficients[counter] = coefficient;
                counter += 1;
            }
        }

        out
    }

    pub(crate) fn from_polynomial_ring_element(re: PolynomialRingElement) -> Self {
        let mut out = Self::ZERO();

        for (i, coefficients) in re
            .coefficients
            .chunks(COEFFICIENTS_IN_SIMD_UNIT)
            .enumerate()
        {
            out.simd_units[i] = SIMDUnit::from_i32_array(coefficients);
        }

        out
    }

    #[inline(always)]
    pub(crate) fn add(&self, rhs: &Self) -> Self {
        let mut sum = Self::ZERO();

        for i in 0..sum.simd_units.len() {
            sum.simd_units[i] = SIMDUnit::add(&self.simd_units[i], &rhs.simd_units[i]);
        }

        sum
    }

    #[inline(always)]
    pub(crate) fn subtract(&self, rhs: &Self) -> Self {
        let mut difference = Self::ZERO();

        for i in 0..difference.simd_units.len() {
            difference.simd_units[i] = SIMDUnit::subtract(&self.simd_units[i], &rhs.simd_units[i]);
        }

        difference
    }
}
