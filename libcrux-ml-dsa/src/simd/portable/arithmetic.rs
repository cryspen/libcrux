use crate::{
    constants::BITS_IN_LOWER_PART_OF_T,
    simd::{
        portable::PortableSIMDUnit,
        traits::{
            FieldElementTimesMontgomeryR, Operations, FIELD_MODULUS,
            INVERSE_OF_MODULUS_MOD_MONTGOMERY_R,
        },
    },
};

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i32;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R^(-1) (mod FIELD_MODULUS).
/// We use 'mfe' as a shorthand for this type
pub type MontgomeryFieldElement = i32;

pub(crate) const MONTGOMERY_SHIFT: u8 = 32;

#[inline(always)]
pub fn add(lhs: &PortableSIMDUnit, rhs: &PortableSIMDUnit) -> PortableSIMDUnit {
    let mut sum = PortableSIMDUnit::ZERO();

    for i in 0..sum.coefficients.len() {
        sum.coefficients[i] = lhs.coefficients[i] + rhs.coefficients[i];
    }

    sum
}

#[inline(always)]
pub fn subtract(lhs: &PortableSIMDUnit, rhs: &PortableSIMDUnit) -> PortableSIMDUnit {
    let mut difference = PortableSIMDUnit::ZERO();

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
    let mut product = PortableSIMDUnit::ZERO();

    for i in 0..product.coefficients.len() {
        product.coefficients[i] =
            montgomery_reduce_element((lhs.coefficients[i] as i64) * (rhs.coefficients[i] as i64))
    }

    product
}

// Splits t ∈ {0, ..., q-1} into t0 and t1 with a = t1*2ᴰ + t0
// and -2ᴰ⁻¹ < t0 < 2ᴰ⁻¹.  Returns t0 and t1 computed as.
//
// - t0 = t mod± 2ᵈ
// - t1 = (t - t0) / 2ᵈ.
//
// We assume the input t is in the signed representative range and convert it
// to the standard unsigned range.
#[inline(always)]
fn power2round_element(t: i32) -> (i32, i32) {
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

pub fn power2round(simd_unit: PortableSIMDUnit) -> (PortableSIMDUnit, PortableSIMDUnit) {
    let mut t0_simd_unit = PortableSIMDUnit::ZERO();
    let mut t1_simd_unit = PortableSIMDUnit::ZERO();

    for (i, t) in simd_unit.coefficients.into_iter().enumerate() {
        let (t0, t1) = power2round_element(t);

        t0_simd_unit.coefficients[i] = t0;
        t1_simd_unit.coefficients[i] = t1;
    }

    (t0_simd_unit, t1_simd_unit)
}

// TODO: Revisit this function when doing the range analysis and testing
// additional KATs.
#[inline(always)]
pub fn infinity_norm_exceeds(simd_unit: PortableSIMDUnit, bound: i32) -> bool {
    let mut exceeds = false;

    // It is ok to leak which coefficient violates the bound since
    // the probability for each coefficient is independent of secret
    // data but we must not leak the sign of the centralized representative.
    //
    // TODO: We can break out of this loop early if need be, but the most
    // straightforward way to do so (returning false) will not go through hax;
    // revisit if performance is impacted.
    for coefficient in simd_unit.coefficients.into_iter() {
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

#[inline(always)]
fn reduce_element(fe: FieldElement) -> FieldElement {
    let quotient = (fe + (1 << 22)) >> 23;

    fe - (quotient * FIELD_MODULUS)
}

#[inline(always)]
pub fn shift_left_then_reduce<const SHIFT_BY: i32>(
    simd_unit: PortableSIMDUnit,
) -> PortableSIMDUnit {
    let mut out = PortableSIMDUnit::ZERO();

    for i in 0..simd_unit.coefficients.len() {
        out.coefficients[i] = reduce_element(simd_unit.coefficients[i] << SHIFT_BY);
    }

    out
}

#[inline(always)]
fn compute_one_hint<const GAMMA2: i32>(low: i32, high: i32) -> i32 {
    if (low > GAMMA2) || (low < -GAMMA2) || (low == -GAMMA2 && high != 0) {
        1
    } else {
        0
    }
}

#[inline(always)]
pub fn compute_hint<const GAMMA2: i32>(
    low: PortableSIMDUnit,
    high: PortableSIMDUnit,
) -> (usize, PortableSIMDUnit) {
    let mut hint = PortableSIMDUnit::ZERO();
    let mut one_hints_count = 0;

    for i in 0..hint.coefficients.len() {
        hint.coefficients[i] =
            compute_one_hint::<GAMMA2>(low.coefficients[i], high.coefficients[i]);
        one_hints_count += hint.coefficients[i] as usize;
    }

    (one_hints_count, hint)
}

// Take a representative -q < r < q and convert it
// to the standard unsigned one in the interval [0, q).
//
// Splits this representative r into r₀ and r₁ such that:
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
#[allow(non_snake_case)]
#[inline(always)]
fn decompose_element<const GAMMA2: i32>(r: i32) -> (i32, i32) {
    debug_assert!(
        r > -FIELD_MODULUS && r < FIELD_MODULUS,
        "the representative is {}",
        r
    );

    // Convert the signed representative to the standard unsigned one.
    let r = r + ((r >> 31) & FIELD_MODULUS);

    let ALPHA = GAMMA2 * 2;

    let r1 = {
        // Compute ⌈r / 128⌉
        let ceil_of_r_by_128 = (r + 127) >> 7;

        match ALPHA {
            190_464 => {
                // We approximate 1 / 1488 as:
                // ⌊2²⁴ / 1488⌋ / 2²⁴ = 11,275 / 2²⁴
                let result = ((ceil_of_r_by_128 * 11_275) + (1 << 23)) >> 24;

                // For the corner-case a₁ = (q-1)/α = 44, we have to set a₁=0.
                (result ^ (43 - result) >> 31) & result
            }
            523_776 => {
                // We approximate 1 / 4092 as:
                // ⌊2²² / 4092⌋ / 2²² = 1025 / 2²²
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

#[inline(always)]
pub(crate) fn use_one_hint<const GAMMA2: i32>(r: i32, hint: i32) -> i32 {
    let (r0, r1) = decompose_element::<GAMMA2>(r);

    if hint == 0 {
        return r1;
    }

    match GAMMA2 {
        95_232 => {
            if r0 > 0 {
                if r1 == 43 {
                    0
                } else {
                    r1 + hint
                }
            } else if r1 == 0 {
                43
            } else {
                r1 - hint
            }
        }

        261_888 => {
            if r0 > 0 {
                (r1 + hint) & 15
            } else {
                (r1 - hint) & 15
            }
        }

        _ => unreachable!(),
    }
}

#[inline(always)]
pub fn decompose<const GAMMA2: i32>(
    simd_unit: PortableSIMDUnit,
) -> (PortableSIMDUnit, PortableSIMDUnit) {
    let mut low = PortableSIMDUnit::ZERO();
    let mut high = PortableSIMDUnit::ZERO();

    for i in 0..low.coefficients.len() {
        let (low_part, high_part) = decompose_element::<GAMMA2>(simd_unit.coefficients[i]);
        low.coefficients[i] = low_part;
        high.coefficients[i] = high_part;
    }

    (low, high)
}

#[inline(always)]
pub fn use_hint<const GAMMA2: i32>(
    simd_unit: PortableSIMDUnit,
    hint: PortableSIMDUnit,
) -> PortableSIMDUnit {
    let mut result = PortableSIMDUnit::ZERO();

    for i in 0..result.coefficients.len() {
        result.coefficients[i] =
            use_one_hint::<GAMMA2>(simd_unit.coefficients[i], hint.coefficients[i]);
    }

    result
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

    #[test]
    fn test_use_one_hint() {
        assert_eq!(use_one_hint::<95_232>(7622170, 0), 40);
        assert_eq!(use_one_hint::<95_232>(2332762, 1), 13);

        assert_eq!(use_one_hint::<261_888>(7691572, 0), 15);
        assert_eq!(use_one_hint::<261_888>(6635697, 1), 12);
    }
}
