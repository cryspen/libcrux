use super::type_definition::*;
use crate::simd::traits::{FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R^(-1) (mod FIELD_MODULUS).
/// We use 'mfe' as a shorthand for this type
pub type MontgomeryFieldElement = i32;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub(crate) type FieldElementTimesMontgomeryR = i32;

pub(crate) const MONTGOMERY_SHIFT: u8 = 32;

#[inline(always)]
pub fn add(lhs: &PortableSIMDUnit, rhs: &PortableSIMDUnit) -> PortableSIMDUnit {
    let mut sum = ZERO();

    for i in 0..sum.coefficients.len() {
        sum.coefficients[i] = lhs.coefficients[i] + rhs.coefficients[i];
    }

    sum
}

#[inline(always)]
pub fn subtract(lhs: &PortableSIMDUnit, rhs: &PortableSIMDUnit) -> PortableSIMDUnit {
    let mut difference = ZERO();

    for i in 0..difference.coefficients.len() {
        difference.coefficients[i] = lhs.coefficients[i] - rhs.coefficients[i];
    }

    difference
}

#[inline(always)]
pub(crate) fn get_n_least_significant_bits(n: u8, value: u64) -> u64 {
    value & ((1 << n) - 1)
}
#[inline(always)]
pub(crate) fn montgomery_reduce_element(value: i64) -> MontgomeryFieldElement {
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
    montgomery_reduce_element((fe as i64) * (fer as i64))
}

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constant(
    mut simd_unit: PortableSIMDUnit,
    c: i32,
) -> PortableSIMDUnit {
    for i in 0..simd_unit.coefficients.len() {
        simd_unit.coefficients[i] =
            montgomery_reduce_element((simd_unit.coefficients[i] as i64) * (c as i64))
    }

    simd_unit
}

#[inline(always)]
pub(crate) fn montgomery_multiply(
    lhs: &PortableSIMDUnit,
    rhs: &PortableSIMDUnit,
) -> PortableSIMDUnit {
    let mut product = ZERO();

    for i in 0..product.coefficients.len() {
        product.coefficients[i] =
            montgomery_reduce_element((lhs.coefficients[i] as i64) * (rhs.coefficients[i] as i64))
    }

    product
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_montgomery_reduce_element() {
        assert_eq!(montgomery_reduce_element(10933346042510), -1553279);
        assert_eq!(montgomery_reduce_element(-20392060523118), 1331779);
        assert_eq!(montgomery_reduce_element(13704140696092), -1231016);
        assert_eq!(montgomery_reduce_element(-631922212176), -2580954);
    }
}
