use crate::simd::traits::{Operations, COEFFICIENTS_IN_SIMD_UNIT};

pub(crate) const SIMD_UNITS_IN_RING_ELEMENT: usize =
    crate::constants::COEFFICIENTS_IN_RING_ELEMENT / COEFFICIENTS_IN_SIMD_UNIT;

#[derive(Clone)]
pub(crate) struct PolynomialRingElement<SIMDUnit: Operations> {
    pub(crate) simd_units: [SIMDUnit; SIMD_UNITS_IN_RING_ELEMENT],
}
impl<SIMDUnit: Operations> PolynomialRingElement<SIMDUnit> {
    #[allow(non_snake_case)]
    pub(crate) fn ZERO() -> Self {
        Self {
            simd_units: core::array::from_fn(|_| SIMDUnit::ZERO()),
        }
    }

    // This is useful for debugging.
    #[allow(dead_code)]
    pub(crate) fn to_i32_array(&self) -> [i32; 256] {
        let mut result = [0i32; 256];

        for (i, simd_unit) in self.simd_units.iter().enumerate() {
            result[i * COEFFICIENTS_IN_SIMD_UNIT..(i + 1) * COEFFICIENTS_IN_SIMD_UNIT]
                .copy_from_slice(&simd_unit.to_coefficient_array());
        }

        result
    }

    // This is useful for debugging.
    #[allow(dead_code)]
    pub(crate) fn from_i32_array(array: &[i32]) -> Self {
        debug_assert!(array.len() >= 256);

        let mut array_chunks = array.chunks(COEFFICIENTS_IN_SIMD_UNIT);

        let mut result = Self::ZERO();

        for i in 0..SIMD_UNITS_IN_RING_ELEMENT {
            result.simd_units[i] = SIMDUnit::from_coefficient_array(&array_chunks.next().unwrap());
        }
        result
    }

    pub(crate) fn infinity_norm_exceeds(&self, bound: i32) -> bool {
        let mut exceeds = false;

        for simd_unit in &self.simd_units {
            exceeds |= SIMDUnit::infinity_norm_exceeds(simd_unit, bound);
        }

        exceeds
    }

    #[inline(always)]
    pub(crate) fn add(&mut self, rhs: &Self) {
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
}
