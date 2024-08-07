use super::vector_type::*;
use crate::vector::{
    traits::FIELD_ELEMENTS_IN_VECTOR, FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R,
};
//#[cfg(hax)]
use hax_lib::*;
use hax_lib::int::*;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R^(-1) (mod FIELD_MODULUS).
/// We use 'mfe' as a shorthand for this type
pub type MontgomeryFieldElement = i16;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub type FieldElementTimesMontgomeryR = i16;

pub(crate) const MONTGOMERY_SHIFT: u8 = 16;
pub(crate) const MONTGOMERY_R: i32 = 1 << MONTGOMERY_SHIFT;

pub(crate) const MONTGOMERY_R_INV: i32 = 169;

pub(crate) const BARRETT_SHIFT: i32 = 26;
pub(crate) const BARRETT_R: i32 = 1 << BARRETT_SHIFT;
/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
pub(crate) const BARRETT_MULTIPLIER: i32 = 20159;

#[cfg_attr(hax, hax_lib::requires(n == 4 || n == 5 || n == 10 || n == 11 || n == MONTGOMERY_SHIFT))]
#[cfg_attr(hax, hax_lib::ensures(|result| result < 2u32.pow(n.into())))]
#[inline(always)]
pub(crate) fn get_n_least_significant_bits(n: u8, value: u32) -> u32 {
    let res = value & ((1 << n) - 1);
    hax_lib::fstar!("calc (==) {
            v res;
            (==) { }
            v (logand value ((1ul <<! n) -! 1ul));
            (==) {mk_int_equiv_lemma #u32_inttype 1} 
            v (logand value (((mk_int 1) <<! n) -! (mk_int 1)));
            (==) { }
            v (logand value (mk_int ((1 * pow2 (v n)) % pow2 32) -! (mk_int 1)));
            (==) {Math.Lemmas.small_mod (pow2 (v n)) (pow2 32); Math.Lemmas.pow2_lt_compat 32 (v n)}
            v (logand value ((mk_int (pow2 (v n))) -! (mk_int 1)));
            (==) {Math.Lemmas.pow2_lt_compat 32 (v n); logand_mask_lemma value (v n)}
            v $value % (pow2 (v n));
        };
        assert (v res < pow2 (v n))");
    res
}

#[hax_lib::requires(hax_lib::forall(|i:usize| (i >= FIELD_ELEMENTS_IN_VECTOR) || 
      (lhs.elements[i].lift() + rhs.elements[i].lift() >= i16::MIN.lift() && 
      lhs.elements[i].lift() + rhs.elements[i].lift() <= i16::MAX.lift()))
)]
#[inline(always)]
pub fn add(mut lhs: PortableVector, rhs: &PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs.elements[i] += rhs.elements[i];
    }

    lhs
}

#[inline(always)]
pub fn sub(mut lhs: PortableVector, rhs: &PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs.elements[i] -= rhs.elements[i];
    }

    lhs
}

#[inline(always)]
pub fn multiply_by_constant(mut v: PortableVector, c: i16) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] *= c;
    }

    v
}

#[inline(always)]
pub fn bitwise_and_with_constant(mut v: PortableVector, c: i16) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] &= c;
    }

    v
}

#[inline(always)]
pub fn shift_right<const SHIFT_BY: i32>(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = v.elements[i] >> SHIFT_BY;
    }

    v
}

// #[inline(always)]
// pub fn shift_left<const SHIFT_BY: i32>(mut lhs: PortableVector) -> PortableVector {
//     for i in 0..FIELD_ELEMENTS_IN_VECTOR {
//         lhs.elements[i] = lhs.elements[i] << SHIFT_BY;
//     }

//     lhs
// }

#[inline(always)]
pub fn cond_subtract_3329(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        hax_lib::debug_assert!(v.elements[i] >= 0 && v.elements[i] < 4096);
        if v.elements[i] >= 3329 {
            v.elements[i] -= 3329
        }
    }
    v
}

/// Signed Barrett Reduction
///
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
///
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
///
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
///
/// In particular, if `|value| < BARRETT_R`, then `|result| < FIELD_MODULUS`.
#[hax_lib::fstar::before("#push-options \"--z3rlimit 250\"")]
#[hax_lib::fstar::after("#pop-options")]
#[cfg_attr(hax, hax_lib::requires((i32::from(value) >= -31625 && i32::from(value) <= 31625)))]
#[cfg_attr(hax, hax_lib::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS))]
pub(crate) fn barrett_reduce_element(value: FieldElement) -> FieldElement {
    // hax_debug_assert!(
    //     i32::from(value) > -BARRETT_R && i32::from(value) < BARRETT_R,
    //     "value is {value}"
    // );

    let t = (i32::from(value) * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    hax_lib::fstar!("assert_norm (v $BARRETT_MULTIPLIER == (pow2 27 + 3329) / (2*3329));
        assert (v $t = v $value * v $BARRETT_MULTIPLIER + pow2 25)");
    let quotient = (t >> BARRETT_SHIFT) as i16;
    hax_lib::fstar!("assert (v $quotient = v $t / pow2 26)");

    let result = value - (quotient * FIELD_MODULUS);
    hax_lib::fstar!("calc (==) {
            v $result % 3329;
            (==) { }
            (v $value - (v $quotient * 3329)) % 3329;
            (==) {Math.Lemmas.lemma_mod_sub_distr (v $value) (v $quotient * 3329) 3329}
            (v $value - (v $quotient * 3329) % 3329) % 3329;
            (==) {Math.Lemmas.cancel_mul_mod (v $quotient) 3329}
            (v $value - 0) % 3329;    
            (==) {}
            (v $value) % 3329;    
        }");

    // hax_debug_assert!(
    //     result > -FIELD_MODULUS && result < FIELD_MODULUS,
    //     "value is {value}"
    // );

    result
}

#[inline(always)]
pub(crate) fn barrett_reduce(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = barrett_reduce_element(v.elements[i]);
    }

    v
}

/// Signed Montgomery Reduction
///
/// Given an input `value`, `montgomery_reduce` outputs a representative `o`
/// such that:
///
/// - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
/// - the absolute value of `o` is bound as follows:
///
/// `|result| ≤ (|value| / MONTGOMERY_R) + (FIELD_MODULUS / 2)
///
/// In particular, if `|value| ≤ FIELD_MODULUS * MONTGOMERY_R`, then `|o| < (3 · FIELD_MODULUS) / 2`.
#[cfg_attr(hax, hax_lib::requires(value >= -(FIELD_MODULUS as i32) * MONTGOMERY_R && value <= (FIELD_MODULUS as i32) * MONTGOMERY_R))]
//#[cfg_attr(hax, hax_lib::ensures(|result| result >= -(3 * FIELD_MODULUS) / 2 && result <= (3 * FIELD_MODULUS) / 2))]
pub(crate) fn montgomery_reduce_element(value: i32) -> MontgomeryFieldElement {
    // This forces hax to extract code for MONTGOMERY_R before it extracts code
    // for this function. The removal of this line is being tracked in:
    // https://github.com/cryspen/libcrux/issues/134
    let _ = MONTGOMERY_R;
    hax_lib::fstar!("assert_norm((v 169l * pow2 16) % 3329 == 1)");

    //hax_debug_assert!(
    //    value >= -FIELD_MODULUS * MONTGOMERY_R && value <= FIELD_MODULUS * MONTGOMERY_R,
    //    "value is {value}"
    //);

    let t0 = (value as u16) as u32;
    hax_lib::fstar!("assert (v $t0 = (v $value % pow2 16) % pow2 32);
        Math.Lemmas.pow2_modulo_modulo_lemma_2 (v $value) 32 16;
        assert (v $t0 = v $value % pow2 16)");

    let t = t0 * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    hax_lib::fstar!("assert (v $t = (v $value % pow2 16) * v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R)");
    let k = (t as u16) as u32;
    hax_lib::fstar!("assert (v $k = (v $t % pow2 16) % pow2 32);
        Math.Lemmas.pow2_modulo_modulo_lemma_2 (v $t) 32 16;
        assert (v $k = v $t % pow2 16);
        calc (==) {
            v $k % pow2 16;
            == { }
            v $t % pow2 16;
            == { }
            ((v $value % pow2 16) * v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R) % pow2 16;
            == {Math.Lemmas.lemma_mod_mul_distr_l (v $value) (v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R) (pow2 16)}
            (v $value * v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R) % pow2 16;
        };
        assert_norm((62209 * 3329) % pow2 16 == 1);
        assert((v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R * 3329) % pow2 16 == 1);
        calc (==) {
            (v $k * 3329) % pow2 16;
            == {Math.Lemmas.lemma_mod_mul_distr_l (v $k) 3329 (pow2 16)}
            ((v $k % pow2 16) * 3329) % pow2 16;
            == { }
            ((v $value * v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R) % pow2 16 * 3329) % pow2 16;
            == {Math.Lemmas.lemma_mod_mul_distr_l (v $value * v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R) (3329) (pow2 16)}
            (v $value * v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R * 3329) % pow2 16;   
            == {Math.Lemmas.paren_mul_right (v $value) (v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R) 3329}
            (v $value * (v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R * 3329)) % pow2 16;   
            == {Math.Lemmas.lemma_mod_mul_distr_r (v $value) (v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R * 3329) (pow2 16)}
            (v $value * ((v $INVERSE_OF_MODULUS_MOD_MONTGOMERY_R * 3329) % pow2 16)) % pow2 16;   
            == {Math.Lemmas.mul_one_right_is_same (v $value)}
            (v $value) % pow2 16;   
        };
        Math.Lemmas.modulo_add (pow2 16) (- (v $k * 3329)) (v $value) (v $k * 3329);
        assert ((v $value - v $k * 3329) % pow2 16 == (v $k * 3329 - v $k * 3329) % pow2 16);
        assert ((v $value - v $k * 3329) % v $MONTGOMERY_R == 0)");
    let k_times_modulus = k * (FIELD_MODULUS as u32);

    let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    let value_high = (value >> MONTGOMERY_SHIFT) as i16;
    hax_lib::fstar!("assert (v $value_high = v $value / v $MONTGOMERY_R)");

    let res = value_high - c;
    hax_lib::fstar!("calc (==) {
            v $res;
            == { }
            (v $value_high - v $c);
            == { }
            ((v $value / v $MONTGOMERY_R) - ((v $k * 3329) / v $MONTGOMERY_R));
            == {Math.Lemmas.lemma_div_exact (v $value - v $k * 3329) (v $MONTGOMERY_R)}
            ((v $value - (v $k * 3329)) / v $MONTGOMERY_R);
        };
        calc (==) {
            v $res % 3329;
            == {Math.Lemmas.lemma_div_exact (v $value - v $k * 3329) (v $MONTGOMERY_R)}
            (((v $value - (v $k * 3329)) / v $MONTGOMERY_R) * ((v $MONTGOMERY_R * v $MONTGOMERY_R_INV) % 3329)) % 3329 ;
            == {Math.Lemmas.lemma_mod_mul_distr_r ((v $value - (v $k * 3329)) / v $MONTGOMERY_R) (v $MONTGOMERY_R * v $MONTGOMERY_R_INV) 3329}
            (((v $value - (v $k * 3329)) / v $MONTGOMERY_R) * (v $MONTGOMERY_R * v $MONTGOMERY_R_INV)) % 3329 ;
            == {Math.Lemmas.paren_mul_right ((v $value - (v $k * 3329)) / v $MONTGOMERY_R) (v $MONTGOMERY_R) (v $MONTGOMERY_R_INV)}
            ((((v $value - (v $k * 3329)) / v $MONTGOMERY_R) * v $MONTGOMERY_R) * v $MONTGOMERY_R_INV) % 3329 ;
            == {Math.Lemmas.lemma_div_exact (v $value - v $k * 3329) (v $MONTGOMERY_R)}
            ((v $value - (v $k * 3329)) * v $MONTGOMERY_R_INV) % 3329 ;
            == { }
            ((v $value * v $MONTGOMERY_R_INV) - ((v $k * 3329) * v $MONTGOMERY_R_INV)) % 3329 ;
            == {Math.Lemmas.paren_mul_right (v $k) 3329 (v $MONTGOMERY_R_INV)} 
            ((v $value * v $MONTGOMERY_R_INV) - (v $k * (3329 * v $MONTGOMERY_R_INV))) % 3329 ;
            == {Math.Lemmas.swap_mul 3329 (v $MONTGOMERY_R_INV)} 
            ((v $value * v $MONTGOMERY_R_INV) - (v $k * (v $MONTGOMERY_R_INV * 3329))) % 3329 ;
            == {Math.Lemmas.paren_mul_right (v $k) (v $MONTGOMERY_R_INV) 3329} 
            ((v $value * v $MONTGOMERY_R_INV) - ((v $k * v $MONTGOMERY_R_INV) * 3329)) % 3329 ;
            == {Math.Lemmas.lemma_mod_sub (v $value * v $MONTGOMERY_R_INV) 3329 (v $k * v $MONTGOMERY_R_INV)}
            (v $value * v $MONTGOMERY_R_INV) % 3329 ;
        }");

    res
}

/// If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
/// `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
/// `x · y`, as follows:
///
///    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`
///
/// `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
/// `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
#[inline(always)]
pub(crate) fn montgomery_multiply_fe_by_fer(
    fe: FieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> FieldElement {
    montgomery_reduce_element((fe as i32) * (fer as i32))
}

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constant(mut v: PortableVector, c: i16) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = montgomery_multiply_fe_by_fer(v.elements[i], c)
    }
    v
}
