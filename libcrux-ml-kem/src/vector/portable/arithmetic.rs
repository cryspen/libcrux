use super::vector_type::*;
use crate::vector::traits::{FIELD_ELEMENTS_IN_VECTOR, FIELD_MODULUS, BARRETT_SHIFT, BARRETT_R, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

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

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
pub(crate) const BARRETT_MULTIPLIER: i32 = 20159;

#[hax_lib::fstar::options("--z3rlimit 150 --split_queries always")]
#[cfg_attr(hax, hax_lib::requires(n <= 16))]
#[cfg_attr(hax, hax_lib::ensures(|result| fstar!("v result == v value % pow2(v n)")))]
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
    v value % (pow2 (v n));
    }");
    res
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("${result}.f_elements == Spec.Utils.map2 (+.) (${lhs}.f_elements) (${rhs}.f_elements)"))]
pub fn add(mut lhs: PortableVector, rhs: &PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs.elements[i] = lhs.elements[i].wrapping_add(rhs.elements[i]);
    }

    lhs
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("${result}.f_elements == Spec.Utils.map2 (-.) (${lhs}.f_elements) (${rhs}.f_elements)"))]
pub fn sub(mut lhs: PortableVector, rhs: &PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs.elements[i] = lhs.elements[i].wrapping_sub(rhs.elements[i]);
    }

    lhs
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("${result}.f_elements == Spec.Utils.map_array (fun x -> x *. c) (${v}.f_elements)"))]
pub fn multiply_by_constant(mut v: PortableVector, c: i16) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = v.elements[i].wrapping_mul(c);
    }

    v
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("${result}.f_elements == Spec.Utils.map_array (fun x -> x &. c) (${v}.f_elements)"))]
pub fn bitwise_and_with_constant(mut v: PortableVector, c: i16) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] &= c;
    }

    v
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
#[hax_lib::ensures(|result| fstar!("(v_SHIFT_BY >=. 0l /\\ v_SHIFT_BY <. 16l) ==> ${result}.f_elements == Spec.Utils.map_array (fun x -> x >>! ${SHIFT_BY}) (${v}.f_elements)"))]   
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
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("${result}.f_elements == Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x) (${v}.f_elements)"))]
    pub fn cond_subtract_3329(mut v: PortableVector) -> PortableVector {
    let _vec0 = v;
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
         hax_lib::loop_invariant!(|i: usize| { fstar!("Seq.length ${v}.f_elements == Seq.length ${_vec0}.f_elements")});
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
/// Note: The input bound is 28296 to prevent overflow in the multiplication of quotient by FIELD_MODULUS
/// 
#[hax_lib::fstar::options("--z3rlimit 150")]
#[cfg_attr(hax, hax_lib::requires(fstar!("Spec.Utils.is_i16b 28296 value")))]
#[cfg_attr(hax, hax_lib::ensures(|result| fstar!("Spec.Utils.is_i16b 3328 result /\\
                v result % 3329 == v value % 3329")))]
pub(crate) fn barrett_reduce_element(value: FieldElement) -> FieldElement {
    let t = (i32::from(value) * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    hax_lib::fstar!("assert_norm (v v_BARRETT_MULTIPLIER == (pow2 27 + 3329) / (2*3329));
                     assert (v t = v value * v v_BARRETT_MULTIPLIER + pow2 25)");
    hax_lib::fstar!("assert (v t / pow2 26 < 9)");
    hax_lib::fstar!("assert (v t / pow2 26 > - 9)");
    let quotient = (t >> BARRETT_SHIFT) as i16;
    hax_lib::fstar!("assert (v quotient = v t / pow2 26)");
    hax_lib::fstar!("assert (Spec.Utils.is_i16b 9 quotient)");
    let result = value - (quotient * FIELD_MODULUS);
    hax_lib::fstar!("calc (==) {
    v result % 3329;
    (==) { }
    (v value - (v quotient * 3329)) % 3329;
    (==) {Math.Lemmas.lemma_mod_sub_distr (v value) (v quotient * 3329) 3329}
    (v value - (v quotient * 3329) % 3329) % 3329;
    (==) {Math.Lemmas.cancel_mul_mod (v quotient) 3329}
    (v value - 0) % 3329;    
    (==) {}
    (v value) % 3329;    
    }");
    result
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[cfg_attr(hax, hax_lib::requires(fstar!("Spec.Utils.is_i16b_array 28296 vec.f_elements")))]
#[cfg_attr(hax, hax_lib::ensures(|result| fstar!("Spec.Utils.is_i16b_array 3328 result.f_elements /\\
                Spec.MLKEM.Math.to_spec_array result.f_elements == Spec.MLKEM.Math.to_spec_array vec.f_elements")))]
pub(crate) fn barrett_reduce(mut vec: PortableVector) -> PortableVector {
    let _vec0 = vec;
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        hax_lib::loop_invariant!(|i: usize| { fstar!("Seq.length ${vec}.f_elements == Seq.length ${_vec0}.f_elements /\\
                         (forall j. j >= v i ==> Spec.Utils.is_i16b 28296 (Seq.index ${vec}.f_elements j))") });
        vec.elements[i] = barrett_reduce_element(vec.elements[i]);
    }
    vec
}

/// Signed Montgomery Reduction
///
/// Given an input `value`, `montgomery_reduce` outputs a representative `o`
/// such that:
///
/// - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
/// - the absolute value of `o` is bound as follows:
///
/// `|result| ≤ ceil(|value| / MONTGOMERY_R) + 1665
///
/// In particular, if `|value| ≤ FIELD_MODULUS-1 * FIELD_MODULUS-1`, then `|o| <= FIELD_MODULUS-1`.
/// And, if `|value| ≤ pow2 16 * FIELD_MODULUS-1`, then `|o| <= FIELD_MODULUS + 1664
/// 
#[hax_lib::fstar::options("--z3rlimit 300 --split_queries always")]
#[cfg_attr(hax, hax_lib::requires(fstar!("Spec.Utils.is_i32b (3328 * pow2 16) value ")))]
#[cfg_attr(hax, hax_lib::ensures(|result| fstar!("Spec.Utils.is_i16b (3328 + 1665) result /\\
                (Spec.Utils.is_i32b (3328 * 3328) value ==> Spec.Utils.is_i16b 3328 result) /\\
                v result % 3329 == (v value * 169) % 3329")))]
pub(crate) fn montgomery_reduce_element(value: i32) -> MontgomeryFieldElement {
    // This forces hax to extract code for MONTGOMERY_R before it extracts code
    // for this function. The removal of this line is being tracked in:
    // https://github.com/cryspen/libcrux/issues/134
    let _ = MONTGOMERY_R;

    let k = (value as i16) as i32 * (INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);
    hax_lib::fstar!("assert(v (cast (cast (value <: i32) <: i16) <: i32) == v value @% pow2 16);
                     assert(v k == (v value @% pow2 16) * 62209);
                     assert(v (cast (cast (k <: i32) <: i16) <: i32) == v k @% pow2 16);
                     assert(v (cast (cast (k <: i32) <: i16) <: i32) < pow2 15);
                     assert(v (cast (cast (k <: i32) <: i16) <: i32) >= -pow2 15);
                     assert(v (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32) == 3329)");
    let k_times_modulus = (k as i16 as i32) * (FIELD_MODULUS as i32);
    hax_lib::fstar!("Spec.Utils.lemma_mul_i16b (pow2 15) (3329) (cast (k <: i32) <: i16) Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS;
                     assert (Spec.Utils.is_i32b (pow2 15 * 3329) k_times_modulus)");
    let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    hax_lib::fstar!("assert (v k_times_modulus < pow2 31);
                     assert (v k_times_modulus / pow2 16 < pow2 15);
                     assert (v c == (v k_times_modulus / pow2 16) @% pow2 16);
                     assert(v c == v k_times_modulus / pow2 16); 
                     assert(Spec.Utils.is_i16b 1665 c)");
    let value_high = (value >> MONTGOMERY_SHIFT) as i16;
    hax_lib::fstar!("assert (v value < pow2 31);
                     assert (v value / pow2 16 < pow2 15);
                     assert (v value_high == (v value / pow2 16) @% pow2 16);
                     assert ((v value / pow2 16) < pow2 15 ==> (v value / pow2 16) @% pow2 16 == (v value / pow2 16));
                     assert (v value_high == (v value / pow2 16)); 
                     assert(Spec.Utils.is_i32b (3328 * 3328) value ==> Spec.Utils.is_i16b 169 value_high);
                     assert(Spec.Utils.is_i16b 3328 value_high)");
    let res = value_high - c;
    hax_lib::fstar!("assert(Spec.Utils.is_i16b (3328 + 1665) res)");
    hax_lib::fstar!("assert(Spec.Utils.is_i32b (3328 * 3328) value ==> Spec.Utils.is_i16b 3328 res)");
    hax_lib::fstar!("calc ( == ) {
        v k_times_modulus % pow2 16;
          ( == ) { assert (v k_times_modulus == (v k @% pow2 16) * 3329) }
        ((v k @% pow2 16) * 3329) % pow2 16;
          ( == ) { assert (v k = (v value @% pow2 16) * 62209) }
        ((((v value @% pow2 16) * 62209) @% pow2 16) * 3329) % pow2 16;
          ( == ) {  Math.Lemmas.lemma_mod_sub ((((v value @% pow2 16) * 62209) % pow2 16) * 3329) (pow2 16) 3329 }
        ((((v value @% pow2 16) * 62209) % pow2 16) * 3329) % pow2 16;
          ( == ) {  Math.Lemmas.lemma_mod_mul_distr_l ((v value @% pow2 16) * 62209) 3329 (pow2 16) }
        ((((v value @% pow2 16) * 62209) * 3329) % pow2 16);
          ( == ) {  Math.Lemmas.lemma_mod_mul_distr_r (v value @% pow2 16) (62209 * 3329) (pow2 16) }
        ((v value @% pow2 16) % pow2 16);
          ( == ) { Math.Lemmas.lemma_mod_sub (v value) (pow2 16) 1 }
        (v value) % pow2 16;
        };
      Math.Lemmas.modulo_add (pow2 16) (- (v k_times_modulus)) (v value) (v k_times_modulus);
      assert ((v value - v k_times_modulus) % pow2 16 == 0)");
    hax_lib::fstar!("calc ( == ) {
        v res % 3329;
            ( == ) { assert (v res == v value_high - v c) }
        (v value / pow2 16 - v k_times_modulus / pow2 16) % 3329 ;
            ( == ) { Math.Lemmas.lemma_div_exact (v value - v k_times_modulus) (pow2 16) }
        ((v value - v k_times_modulus) / pow2 16) % 3329;
            ( == ) { assert ((pow2 16 * 169) % 3329 == 1) }
        (((v value - v k_times_modulus) / pow2 16) * ((pow2 16 * 169) % 3329)) % 3329;
            ( == ) { Math.Lemmas.lemma_mod_mul_distr_r ((v value - v k_times_modulus) / pow2 16) (pow2 16 * 169) 3329}
        (((v value - v k_times_modulus) / pow2 16) * pow2 16 * 169) % 3329;
            ( == ) { Math.Lemmas.lemma_div_exact (v value - v k_times_modulus) (pow2 16)}
        ((v value - v k_times_modulus) * 169) % 3329;
            ( == ) { assert (v k_times_modulus == (v k @% pow2 16) * 3329) }
        ((v value * 169) - ((v k @% pow2 16) * 3329 * 169)) % 3329; 
            ( == ) { Math.Lemmas.lemma_mod_sub (v value * 169) 3329 ((v k @% pow2 16) * 169)}
        (v value * 169) % 3329;  
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
#[cfg_attr(hax, hax_lib::requires(fstar!("Spec.Utils.is_i16b 3328 fer")))]
#[cfg_attr(hax, hax_lib::ensures(|result| fstar!("Spec.Utils.is_i16b (3328 + 1665) result /\\
                v result % 3329 == (v fe * v fer * 169) % 3329")))]
pub(crate) fn montgomery_multiply_fe_by_fer(
    fe: FieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> FieldElement {
    hax_lib::fstar!("Spec.Utils.lemma_mul_i16b (pow2 16) (3328) fe fer");
    let product = (fe as i32) * (fer as i32);
    montgomery_reduce_element(product)
}

#[inline(always)]
#[cfg_attr(hax, hax_lib::requires(fstar!("Spec.Utils.is_i16b 3328 c")))]
pub(crate) fn montgomery_multiply_by_constant(mut v: PortableVector, c: i16) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = montgomery_multiply_fe_by_fer(v.elements[i], c)
    }
    v
}
