use crate::{
    helper::cloop,
    simd::traits::{Operations, COEFFICIENTS_IN_SIMD_UNIT, SIMD_UNITS_IN_RING_ELEMENT},
};

#[derive(Clone, Copy)]
pub(crate) struct PolynomialRingElement<SIMDUnit: Operations> {
    pub(crate) simd_units: [SIMDUnit::Coefficient; SIMD_UNITS_IN_RING_ELEMENT],
}

impl<SIMDUnit: Operations> PolynomialRingElement<SIMDUnit> {
    #[allow(non_snake_case)]
    pub(crate) fn ZERO() -> Self {
        Self {
            simd_units: [SIMDUnit::ZERO(); SIMD_UNITS_IN_RING_ELEMENT],
        }
    }

    // This is useful for debugging.
    // XXX: Used in `make_int`
    pub(crate) fn to_i32_array(&self) -> [i32; 256] {
        let mut result = [0i32; 256];

        cloop! {
            for (i, simd_unit) in self.simd_units.iter().enumerate() {
                SIMDUnit::to_coefficient_array(&simd_unit, &mut result[i * COEFFICIENTS_IN_SIMD_UNIT..(i + 1) * COEFFICIENTS_IN_SIMD_UNIT]);
            }
        }

        result
    }

    pub(crate) fn from_i32_array(array: &[i32], result: &mut Self) {
        debug_assert!(array.len() >= 256);
        for i in 0..SIMD_UNITS_IN_RING_ELEMENT {
            result.simd_units[i] = SIMDUnit::from_coefficient_array(
                &array[i * COEFFICIENTS_IN_SIMD_UNIT..(i + 1) * COEFFICIENTS_IN_SIMD_UNIT],
            );
        }
    }

    #[cfg(test)]
    pub(crate) fn from_i32_array_test(array: &[i32]) -> Self {
        let mut result = PolynomialRingElement::ZERO();
        Self::from_i32_array(array, &mut result);
        result
    }

    pub(crate) fn infinity_norm_exceeds(&self, bound: i32) -> bool {
        let mut exceeds = false;

        for i in 0..self.simd_units.len() {
            exceeds = exceeds || SIMDUnit::infinity_norm_exceeds(&self.simd_units[i], bound);
        }

        exceeds
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
    pub(crate) fn add_mut(&mut self, rhs: &Self) {
        for i in 0..self.simd_units.len() {
            self.simd_units[i] = SIMDUnit::add(&self.simd_units[i], &rhs.simd_units[i]);
        }
    }

    #[inline(always)]
    pub(crate) fn subtract(&self, rhs: &Self) -> Self {
        let mut difference = Self::ZERO();

        for i in 0..difference.simd_units.len() {
            difference.simd_units[i] = SIMDUnit::subtract(&self.simd_units[i], &rhs.simd_units[i]);
        }

        difference
    }

    #[inline(always)]
    pub(crate) fn subtract_mut(&mut self, rhs: &Self) {
        for i in 0..self.simd_units.len() {
            self.simd_units[i] = SIMDUnit::subtract(&self.simd_units[i], &rhs.simd_units[i]);
        }
    }
}
