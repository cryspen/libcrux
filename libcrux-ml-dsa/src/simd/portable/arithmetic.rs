use super::vector_type::{Coefficients, FieldElement};
use crate::{
    constants::{Gamma2, BITS_IN_LOWER_PART_OF_T, GAMMA2_V261_888, GAMMA2_V95_232},
    simd::traits::{
        FieldElementTimesMontgomeryR, FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R,
    },
};

pub(crate) const MONTGOMERY_SHIFT: u8 = 32;

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 150")]
#[hax_lib::requires(fstar!(r#"forall i. i < 8 ==> 
    Spec.Utils.is_intb (pow2 31 - 1) (v (Seq.index ${lhs}.f_values i) + v (Seq.index ${rhs}.f_values i))"#))]
#[hax_lib::ensures(|result| fstar!(r#"forall i. i < 8 ==>
    (v (Seq.index ${lhs}_future.f_values i) == 
     v (Seq.index ${lhs}.f_values i) + v (Seq.index ${rhs}.f_values i))"#))]
pub fn add(lhs: &mut Coefficients, rhs: &Coefficients) {
    let _lhs0 = lhs.clone();
    for i in 0..lhs.values.len() {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(
                r#"
              (forall j. j < v i ==> (Seq.index ${lhs}.f_values j) == 
                                     (Seq.index ${_lhs0}.f_values j) +! (Seq.index ${rhs}.f_values j)) /\
              (forall j. j >= v i ==> (Seq.index ${lhs}.f_values j) == (Seq.index ${_lhs0}.f_values j))"#
            )
        });
        lhs.values[i] += rhs.values[i];
    }
    hax_lib::fstar!(
        "assert (forall i. v (Seq.index ${lhs}.f_values i) ==
    			          v (Seq.index ${_lhs0}.f_values i) + v (Seq.index ${rhs}.f_values i))"
    )
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 150")]
#[hax_lib::requires(fstar!(r#"forall i. i < 8 ==> 
    Spec.Utils.is_intb (pow2 31 - 1) (v (Seq.index ${lhs}.f_values i) - v (Seq.index ${rhs}.f_values i))"#))]
#[hax_lib::ensures(|result| fstar!(r#"forall i. i < 8 ==>
    (v (Seq.index ${lhs}_future.f_values i) == 
     v (Seq.index ${lhs}.f_values i) - v (Seq.index ${rhs}.f_values i))"#))]
pub fn subtract(lhs: &mut Coefficients, rhs: &Coefficients) {
    let _lhs0 = lhs.clone();
    for i in 0..lhs.values.len() {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(
                r#"
              (forall j. j < v i ==> (Seq.index ${lhs}.f_values j) == 
                                     (Seq.index ${_lhs0}.f_values j) -! (Seq.index ${rhs}.f_values j)) /\
              (forall j. j >= v i ==> (Seq.index ${lhs}.f_values j) == (Seq.index ${_lhs0}.f_values j))"#
            )
        });
        lhs.values[i] -= rhs.values[i];
    }
    hax_lib::fstar!(
        "assert (forall i. v (Seq.index ${lhs}.f_values i) ==
    			          v (Seq.index ${_lhs0}.f_values i) - v (Seq.index ${rhs}.f_values i))"
    )
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 150 --split_queries always")]
#[hax_lib::requires(n <= 32)]
#[hax_lib::ensures(|result| fstar!(r#"v result == v value % pow2(v n)"#))]
pub(crate) fn get_n_least_significant_bits(n: u8, value: u64) -> u64 {
    let res = value & ((1 << n) - 1);
    hax_lib::fstar!(
        "calc (==) {
    v res;
    (==) { }
    v (logand value (((mk_u64 1) <<! n) -! (mk_u64 1)));
    (==) {} 
    v (logand value (((mk_int 1) <<! n) -! (mk_int 1)));
    (==) { }
    v (logand value (mk_int ((1 * pow2 (v n)) % pow2 64) -! (mk_int 1)));
    (==) {Math.Lemmas.small_mod (pow2 (v n)) (pow2 64); Math.Lemmas.pow2_lt_compat 64 (v n)}
    v (logand value ((mk_int (pow2 (v n))) -! (mk_int 1)));
    (==) {Math.Lemmas.pow2_lt_compat 64 (v n); logand_mask_lemma value (v n)}
    v value % (pow2 (v n));
    }"
    );
    res
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 500 --split_queries always")]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i64b (8380416 * pow2 32) value "#))]
#[hax_lib::ensures(|result| fstar!(r#"Spec.Utils.is_i32b (8380416 + 4190209) result /\
                (Spec.Utils.is_i64b (8380416 * pow2 31) value ==> Spec.Utils.is_i32b 8380416 result) /\
                v result % 8380417 == (v value * 8265825) % 8380417"#))]
pub(crate) fn montgomery_reduce_element(value: i64) -> FieldElementTimesMontgomeryR {
    let t = get_n_least_significant_bits(MONTGOMERY_SHIFT, value as u64)
        * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    hax_lib::fstar!(
        r#"assert (v $t == (v $value % pow2 32) * 58728449)"#
    );
    let k = get_n_least_significant_bits(MONTGOMERY_SHIFT, t) as i32;
    hax_lib::fstar!(
        r#"assert (v $k == v $t @% pow2 32);
        assert(v (cast ($k <: i32) <: i64) == v $k);
        assert(v (cast ($k <: i32) <: i64) < pow2 31);
        assert(v (cast ($k <: i32) <: i64) >= -pow2 31);
        assert(v (cast ($FIELD_MODULUS <: i32) <: i64) == 8380417)"#
    );

    let k_times_modulus = (k as i64) * (FIELD_MODULUS as i64);
    hax_lib::fstar!(
        r#"Spec.Utils.lemma_mul_i32b (pow2 31) (8380417) $k $FIELD_MODULUS;
        assert (Spec.Utils.is_i64b (pow2 31 * 8380417) $k_times_modulus)"#
    );

    let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i32;
    hax_lib::fstar!(
        r#"assert (v $k_times_modulus < pow2 63);
        assert (v $k_times_modulus / pow2 32 < pow2 31);
        assert (v $c == (v $k_times_modulus / pow2 32) @% pow2 32);
        assert(v $c == v $k_times_modulus / pow2 32); 
        assert(Spec.Utils.is_i32b 4190209 $c)"#
    );
    let value_high = (value >> MONTGOMERY_SHIFT) as i32;
    hax_lib::fstar!(
        r#"assert (v $value < pow2 63);
        assert (v $value / pow2 32 < pow2 31);
        assert (v $value_high == (v $value / pow2 32) @% pow2 32);
        Spec.Utils.lemma_div_at_percent (v $value) (pow2 32);
        assert (v $value_high == (v $value / pow2 32));
        assert (Spec.Utils.is_i64b (8380416 * 8380416) $value ==> Spec.Utils.is_i32b 8265825 $value_high);
        assert(Spec.Utils.is_i32b 8380416 $value_high)"#
    );

    let res = value_high - c;
    hax_lib::fstar!(
        r#"assert(Spec.Utils.is_i32b (8380416 + 4190209) $res);
        assert(Spec.Utils.is_i64b (8380416 * pow2 31) $value ==> Spec.Utils.is_i32b 58728448 $res)"#
    );
    hax_lib::fstar!(
        r#"calc ( == ) {
            v $k_times_modulus % pow2 32;
            ( == ) { assert (v $k_times_modulus == v $k * 8380417) }
            (v $k * 8380417) % pow2 32;
            ( == ) { assert (v $k = ((v $value % pow2 32) * 58728449) @% pow2 32) }
            ((((v $value % pow2 32) * 58728449) @% pow2 32) * 8380417) % pow2 32;
            ( == ) {  Math.Lemmas.lemma_mod_sub ((((v $value % pow2 32) * 58728449) % pow2 32) * 8380417) (pow2 32) 8380417 }
            ((((v $value % pow2 32) * 58728449) % pow2 32) * 8380417) % pow2 32;
            ( == ) {  Math.Lemmas.lemma_mod_mul_distr_l ((v $value % pow2 32) * 58728449) 8380417 (pow2 32) }
            ((((v $value % pow2 32) * 58728449) * 8380417) % pow2 32);
            ( == ) {  Math.Lemmas.lemma_mod_mul_distr_r (v $value % pow2 32) (58728449 * 8380417) (pow2 32) }
            ((v $value % pow2 32) % pow2 32);
            ( == ) { Math.Lemmas.lemma_mod_sub (v $value) (pow2 32) 1 }
            (v $value) % pow2 32;
        };
        Math.Lemmas.modulo_add (pow2 32) (- (v $k_times_modulus)) (v $value) (v $k_times_modulus);
        assert ((v $value - v $k_times_modulus) % pow2 32 == 0)"#
    );
    hax_lib::fstar!(
        r#"calc ( == ) {
            v $res % 8380417;
            ( == ) { assert (v $res == v $value_high - v $c) }
            (v $value / pow2 32 - v $k_times_modulus / pow2 32) % 8380417;
            ( == ) { Math.Lemmas.lemma_div_exact (v $value - v $k_times_modulus) (pow2 32) }
            ((v $value - v $k_times_modulus) / pow2 32) % 8380417;
            ( == ) { assert ((pow2 32 * 8265825) % 8380417 == 1) }
            (((v $value - v $k_times_modulus) / pow2 32) * ((pow2 32 * 8265825) % 8380417)) % 8380417;
            ( == ) { Math.Lemmas.lemma_mod_mul_distr_r ((v $value - v $k_times_modulus) / pow2 32)
            (pow2 32 * 8265825)
            8380417 }
            (((v $value - v $k_times_modulus) / pow2 32) * pow2 32 * 8265825) % 8380417;
            ( == ) { Math.Lemmas.lemma_div_exact (v $value - v $k_times_modulus) (pow2 32) }
            ((v $value - v $k_times_modulus) * 8265825) % 8380417;
            ( == ) { assert (v $k_times_modulus == (v $k @% pow2 32) * 8380417) }
            ((v $value * 8265825) - ((v $k @% pow2 32) * 8380417 * 8265825)) % 8380417;
            ( == ) { Math.Lemmas.lemma_mod_sub (v $value * 8265825) 8380417 ((v $k @% pow2 32) * 8265825) }
            (v $value * 8265825) % 8380417;
        }"#
    );
    res
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300")]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i32b 4190208 fer"#))]
#[hax_lib::ensures(|result| fstar!(r#"Spec.Utils.is_i32b 8380416 result /\
                v result % 8380417 == (v fe * v fer * 8265825) % 8380417"#))]
pub(crate) fn montgomery_multiply_fe_by_fer(
    fe: FieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> FieldElement {
    hax_lib::fstar!(r#"Spec.Utils.lemma_mul_i32b (pow2 31) (4190208) fe fer"#);
    montgomery_reduce_element((fe as i64) * (fer as i64))
}

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constant(simd_unit: &mut Coefficients, c: i32) {
    for i in 0..simd_unit.values.len() {
        simd_unit.values[i] = montgomery_reduce_element((simd_unit.values[i] as i64) * (c as i64))
    }
}

#[inline(always)]
pub(crate) fn montgomery_multiply(lhs: &mut Coefficients, rhs: &Coefficients) {
    for i in 0..lhs.values.len() {
        lhs.values[i] = montgomery_reduce_element((lhs.values[i] as i64) * (rhs.values[i] as i64))
    }
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
    // Hax issue: https://github.com/hacspec/hax/issues/1082
    debug_assert!(t > -FIELD_MODULUS && t < FIELD_MODULUS);

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

#[inline(always)]
pub(super) fn power2round(t0: &mut Coefficients, t1: &mut Coefficients) {
    for i in 0..t0.values.len() {
        (t0.values[i], t1.values[i]) = power2round_element(t0.values[i]);
    }
}

// TODO: Revisit this function when doing the range analysis and testing
// additional KATs.
#[inline(always)]
pub(super) fn infinity_norm_exceeds(simd_unit: &Coefficients, bound: i32) -> bool {
    let mut result = false;
    // It is ok to leak which coefficient violates the bound since
    // the probability for each coefficient is independent of secret
    // data but we must not leak the sign of the centralized representative.
    for i in 0..simd_unit.values.len() {
        let coefficient = simd_unit.values[i];
        debug_assert!(coefficient > -FIELD_MODULUS && coefficient < FIELD_MODULUS);
        // This norm is calculated using the absolute value of the
        // signed representative in the range:
        //
        // -FIELD_MODULUS / 2 < r <= FIELD_MODULUS / 2.
        //
        // So if the coefficient is negative, get its absolute value, but
        // don't convert it into a different representation.
        let sign = coefficient >> 31;
        let normalized = coefficient - (sign & (2 * coefficient));

        // FIXME: return
        // [hax] https://github.com/hacspec/hax/issues/1204
        result = result || normalized >= bound;
    }

    result
}

#[inline(always)]
fn reduce_element(fe: FieldElement) -> FieldElement {
    let quotient = (fe + (1 << 22)) >> 23;

    fe - (quotient * FIELD_MODULUS)
}

#[inline(always)]
pub(super) fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Coefficients) {
    for i in 0..simd_unit.values.len() {
        simd_unit.values[i] = reduce_element(simd_unit.values[i] << SHIFT_BY);
    }
}

#[inline(always)]
fn compute_one_hint(low: i32, high: i32, gamma2: i32) -> i32 {
    if (low > gamma2) || (low < -gamma2) || (low == -gamma2 && high != 0) {
        1
    } else {
        0
    }
}

#[inline(always)]
pub(super) fn compute_hint(
    low: &Coefficients,
    high: &Coefficients,
    gamma2: i32,
    hint: &mut Coefficients,
) -> usize {
    let mut one_hints_count = 0;

    for i in 0..hint.values.len() {
        hint.values[i] = compute_one_hint(low.values[i], high.values[i], gamma2);
        one_hints_count += hint.values[i] as usize;
    }

    one_hints_count
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
#[inline(always)]
fn decompose_element(gamma2: Gamma2, r: i32) -> (i32, i32) {
    debug_assert!(r > -FIELD_MODULUS && r < FIELD_MODULUS);

    // Convert the signed representative to the standard unsigned one.
    let r = r + ((r >> 31) & FIELD_MODULUS);

    let r1 = {
        // Compute ⌈r / 128⌉
        let ceil_of_r_by_128 = (r + 127) >> 7;

        match gamma2 {
            GAMMA2_V95_232 => {
                // We approximate 1 / 1488 as:
                // ⌊2²⁴ / 1488⌋ / 2²⁴ = 11,275 / 2²⁴
                let result = ((ceil_of_r_by_128 * 11_275) + (1 << 23)) >> 24;

                // For the corner-case a₁ = (q-1)/α = 44, we have to set a₁=0.
                (result ^ (43 - result) >> 31) & result
            }
            GAMMA2_V261_888 => {
                // We approximate 1 / 4092 as:
                // ⌊2²² / 4092⌋ / 2²² = 1025 / 2²²
                let result = (ceil_of_r_by_128 * 1025 + (1 << 21)) >> 22;

                // For the corner-case a₁ = (q-1)/α = 16, we have to set a₁=0.
                result & 15
            }

            _ => unreachable!(),
        }
    };

    let alpha = gamma2 * 2;
    let mut r0 = r - (r1 * alpha);

    // In the corner-case, when we set a₁=0, we will incorrectly
    // have a₀ > (q-1)/2 and we'll need to subtract q.  As we
    // return a₀ + q, that comes down to adding q if a₀ < (q-1)/2.
    r0 -= (((FIELD_MODULUS - 1) / 2 - r0) >> 31) & FIELD_MODULUS;

    (r0, r1)
}

#[inline(always)]
pub(crate) fn use_one_hint(gamma2: Gamma2, r: i32, hint: i32) -> i32 {
    let (r0, r1) = decompose_element(gamma2, r);

    if hint == 0 {
        return r1;
    }

    match gamma2 {
        GAMMA2_V95_232 => {
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

        GAMMA2_V261_888 => {
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
pub fn decompose(
    gamma2: Gamma2,
    simd_unit: &Coefficients,
    low: &mut Coefficients,
    high: &mut Coefficients,
) {
    for i in 0..low.values.len() {
        (low.values[i], high.values[i]) = decompose_element(gamma2, simd_unit.values[i]);
    }
}

#[inline(always)]
pub fn use_hint(gamma2: Gamma2, simd_unit: &Coefficients, hint: &mut Coefficients) {
    for i in 0..hint.values.len() {
        hint.values[i] = use_one_hint(gamma2, simd_unit.values[i], hint.values[i]);
    }
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
        assert_eq!(use_one_hint(GAMMA2_V95_232, 7622170, 0), 40);
        assert_eq!(use_one_hint(GAMMA2_V95_232, 2332762, 1), 13);

        assert_eq!(use_one_hint(GAMMA2_V261_888, 7691572, 0), 15);
        assert_eq!(use_one_hint(GAMMA2_V261_888, 6635697, 1), 12);
    }
}
