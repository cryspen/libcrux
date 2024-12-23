use crate::{
    helper::cloop,
    simd::traits::{Operations, COEFFICIENTS_IN_SIMD_UNIT, SIMD_UNITS_IN_RING_ELEMENT},
};

#[derive(Clone, Copy)]
pub(crate) struct PolynomialRingElement<SIMDUnit: Operations> {
    pub(crate) simd_units: [SIMDUnit::Coefficient; SIMD_UNITS_IN_RING_ELEMENT],
}

impl<SIMDUnit: Operations> PolynomialRingElement<SIMDUnit> {
    pub(crate) fn zero() -> Self {
        Self {
            simd_units: [SIMDUnit::zero(); SIMD_UNITS_IN_RING_ELEMENT],
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
        let mut result = PolynomialRingElement::zero();
        Self::from_i32_array(array, &mut result);
        result
    }

    #[inline(always)]
    pub(crate) fn infinity_norm_exceeds(&self, bound: i32) -> bool {
        for i in 0..self.simd_units.len() {
            if SIMDUnit::infinity_norm_exceeds(&self.simd_units[i], bound) {
                return true;
            }
        }

        false
    }

    #[inline(always)]
    pub(crate) fn add(&mut self, rhs: &Self) {
        for i in 0..self.simd_units.len() {
            SIMDUnit::add(&mut self.simd_units[i], &rhs.simd_units[i]);
        }
    }

    #[inline(always)]
    pub(crate) fn subtract(&mut self, rhs: &Self) {
        for i in 0..self.simd_units.len() {
            SIMDUnit::subtract(&mut self.simd_units[i], &rhs.simd_units[i]);
        }
    }
}
