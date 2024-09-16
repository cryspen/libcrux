use super::arithmetic::*;
use super::vector_type::*;

#[inline(always)]
#[hax_lib::requires(fstar!("v i < 16 /\\ v j < 16 /\\ Spec.Utils.is_i16b 1664 $zeta"))]
#[hax_lib::ensures(|result| fstar!("forall b. (Spec.Utils.is_i16b b ${vec}.f_elements.[i] /\\
                                               Spec.Utils.is_i16b b ${vec}.f_elements.[j]) ==>
                                              (Spec.Utils.is_i16b (b+3328+1665) ${vec}_future.f_elements.[i] /\\
                                               Spec.Utils.is_i16b (b+3328+1665) ${vec}_future.f_elements.[j])"))]
pub(crate) fn ntt_step(vec: &mut PortableVector, zeta: i16, i: usize, j: usize) {
    let t = montgomery_multiply_fe_by_fer(vec.elements[j], zeta);
    vec.elements[j] = vec.elements[i] - t;
    vec.elements[i] = vec.elements[i] + t;
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax_lib::requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1 /\\ Spec.Utils.is_i16b 1664 zeta2 /\\ Spec.Utils.is_i16b 1664 zeta3"))]
pub(crate) fn ntt_layer_1_step(
    mut vec: PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    ntt_step(&mut vec, zeta0, 0, 2);
    ntt_step(&mut vec, zeta0, 1, 3);
    ntt_step(&mut vec, zeta1, 4, 6);
    ntt_step(&mut vec, zeta1, 5, 7);
    ntt_step(&mut vec, zeta2, 8, 10);
    ntt_step(&mut vec, zeta2, 9, 11);
    ntt_step(&mut vec, zeta3, 12, 14);
    ntt_step(&mut vec, zeta3, 13, 15);
    vec
}

#[inline(always)]
#[hax_lib::requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1"))]
pub(crate) fn ntt_layer_2_step(mut vec: PortableVector, zeta0: i16, zeta1: i16) -> PortableVector {
    ntt_step(&mut vec, zeta0, 0, 4);
    ntt_step(&mut vec, zeta0, 1, 5);
    ntt_step(&mut vec, zeta0, 2, 6);
    ntt_step(&mut vec, zeta0, 3, 7);
    ntt_step(&mut vec, zeta1, 8, 12);
    ntt_step(&mut vec, zeta1, 9, 13);
    ntt_step(&mut vec, zeta1, 10, 14);
    ntt_step(&mut vec, zeta1, 11, 15);
    vec
}

#[inline(always)]
#[hax_lib::requires(fstar!("Spec.Utils.is_i16b 1664 zeta"))]
pub(crate) fn ntt_layer_3_step(mut vec: PortableVector, zeta: i16) -> PortableVector {
    ntt_step(&mut vec, zeta, 0, 8);
    ntt_step(&mut vec, zeta, 1, 9);
    ntt_step(&mut vec, zeta, 2, 10);
    ntt_step(&mut vec, zeta, 3, 11);
    ntt_step(&mut vec, zeta, 4, 12);
    ntt_step(&mut vec, zeta, 5, 13);
    ntt_step(&mut vec, zeta, 6, 14);
    ntt_step(&mut vec, zeta, 7, 15);
    vec
}

#[inline(always)]
#[hax_lib::requires(fstar!("v i < 16 /\\ v j < 16 /\\ Spec.Utils.is_i16b 1664 $zeta /\\
                        Spec.Utils.is_i16b_array (3328 + 1665) ${vec}.f_elements"))]
#[hax_lib::ensures(|result| fstar!("Spec.Utils.is_i16b_array (3328 + 1665) ${vec}_future.f_elements"))]
pub(crate) fn inv_ntt_step(vec: &mut PortableVector, zeta: i16, i: usize, j: usize) {
    let a_minus_b = vec.elements[j] - vec.elements[i];
    vec.elements[i] = barrett_reduce_element(vec.elements[i] + vec.elements[j]);
    vec.elements[j] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax_lib::requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1 /\\
                            Spec.Utils.is_i16b 1664 zeta2 /\\ Spec.Utils.is_i16b 1664 zeta3 /\\
                            Spec.Utils.is_i16b_array (3328 + 1665) ${vec}.f_elements"))]
#[hax_lib::ensures(|result| fstar!("Spec.Utils.is_i16b_array (3328 + 1665) ${result}.f_elements"))]
pub(crate) fn inv_ntt_layer_1_step(
    mut vec: PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    inv_ntt_step(&mut vec, zeta0, 0, 2);
    inv_ntt_step(&mut vec, zeta0, 1, 3);
    inv_ntt_step(&mut vec, zeta1, 4, 6);
    inv_ntt_step(&mut vec, zeta1, 5, 7);
    inv_ntt_step(&mut vec, zeta2, 8, 10);
    inv_ntt_step(&mut vec, zeta2, 9, 11);
    inv_ntt_step(&mut vec, zeta3, 12, 14);
    inv_ntt_step(&mut vec, zeta3, 13, 15);
    vec
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax_lib::requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1 /\\
                            Spec.Utils.is_i16b_array (3328 + 1665) ${vec}.f_elements"))]
#[hax_lib::ensures(|result| fstar!("Spec.Utils.is_i16b_array (3328 + 1665) ${result}.f_elements"))]
pub(crate) fn inv_ntt_layer_2_step(
    mut vec: PortableVector,
    zeta0: i16,
    zeta1: i16,
) -> PortableVector {
    inv_ntt_step(&mut vec, zeta0, 0, 4);
    inv_ntt_step(&mut vec, zeta0, 1, 5);
    inv_ntt_step(&mut vec, zeta0, 2, 6);
    inv_ntt_step(&mut vec, zeta0, 3, 7);
    inv_ntt_step(&mut vec, zeta1, 8, 12);
    inv_ntt_step(&mut vec, zeta1, 9, 13);
    inv_ntt_step(&mut vec, zeta1, 10, 14);
    inv_ntt_step(&mut vec, zeta1, 11, 15);
    vec
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax_lib::requires(fstar!("Spec.Utils.is_i16b 1664 zeta /\\
                            Spec.Utils.is_i16b_array (3328 + 1665) ${vec}.f_elements"))]
#[hax_lib::ensures(|result| fstar!("Spec.Utils.is_i16b_array (3328 + 1665) ${result}.f_elements"))]
pub(crate) fn inv_ntt_layer_3_step(mut vec: PortableVector, zeta: i16) -> PortableVector {
    inv_ntt_step(&mut vec, zeta, 0, 8);
    inv_ntt_step(&mut vec, zeta, 1, 9);
    inv_ntt_step(&mut vec, zeta, 2, 10);
    inv_ntt_step(&mut vec, zeta, 3, 11);
    inv_ntt_step(&mut vec, zeta, 4, 12);
    inv_ntt_step(&mut vec, zeta, 5, 13);
    inv_ntt_step(&mut vec, zeta, 6, 14);
    inv_ntt_step(&mut vec, zeta, 7, 15);
    vec
}

/// Compute the product of two Kyber binomials with respect to the
/// modulus `X² - zeta`.
///
/// This function almost implements <strong>Algorithm 11</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
///
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
///
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
/// We say "almost" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[inline(always)]
#[hax_lib::requires(fstar!("v i < 16 /\\ v j < 16 /\\ Spec.Utils.is_i16b 1664 $zeta /\\
        Spec.Utils.is_i16b_array 3228 ${a}.f_elements /\\
        Spec.Utils.is_i16b_array 3228 ${b}.f_elements "))]
#[hax_lib::ensures(|()| fstar!("
        (forall k. (k <> v $i /\\ k <> v $j) ==> 
                    Seq.index out_future.f_elements k == Seq.index out.f_elements k) /\\                 
         (let ai = Seq.index ${a}.f_elements (v $i) in
          let aj = Seq.index ${a}.f_elements (v $j) in
          let bi = Seq.index ${b}.f_elements (v $i) in
          let bj = Seq.index ${b}.f_elements (v $j) in
          let oi = Seq.index out_future.f_elements (v $i) in
          let oj = Seq.index out_future.f_elements (v $j) in
          let (x,y) = 
          Spec.MLKEM.Math.poly_base_case_multiply 
             ((v ai * 169) % 3329)
             ((v aj * 169) % 3329)
             ((v bi * 169) % 3329)
             ((v bj * 169) % 3329)
             ((v zeta * 169) % 3329) in
          (x == ((v oi * 169) % 3329) /\\
           y == ((v oj * 169) % 3329)))"))]
pub(crate) fn ntt_multiply_binomials(
    a: &PortableVector,
    b: &PortableVector,
    zeta: FieldElementTimesMontgomeryR,
    i: usize,
    j: usize,
    out: &mut PortableVector,
) {
    let ai = a.elements[i];
    let bi = b.elements[i];
    let aj = a.elements[j];
    let bj = b.elements[j];
    hax_lib::fstar!("assert(Spec.Utils.is_i16b 3328 $ai);
                     assert(Spec.Utils.is_i16b 3328 $bi);
                     assert(Spec.Utils.is_i16b 3328 $aj);
                     assert(Spec.Utils.is_i16b 3328 $bj);
                     assert_norm (3328 * 3328 < pow2 31);
                     assert_norm (3328 * 3328 <= 3328 * pow2 15);
                     assert_norm (3328 * 3328 + 3328 * 1664 <= 3328 * pow2 15);
                     assert_norm (3328 * 3328 + 3328 * 3328 <= 3328 * pow2 15)");
    hax_lib::fstar!("Spec.Utils.lemma_mul_i16b 3328 3328 $ai $bi;
                     Spec.Utils.lemma_mul_i16b 3328 3328 $aj $bj;
                     Spec.Utils.lemma_mul_i16b 3328 3328 $ai $bj;
                     Spec.Utils.lemma_mul_i16b 3328 3328 $aj $bi");
    let ai_bi = (ai as i32) * (bi as i32);
    let aj_bj_ = (aj as i32) * (bj as i32);
    let aj_bj = montgomery_reduce_element(aj_bj_);
    hax_lib::fstar!("Spec.Utils.lemma_mul_i16b 3328 1664 $aj_bj $zeta");
    let aj_bj_zeta = (aj_bj as i32) * (zeta as i32);
    let ai_bi_aj_bj = ai_bi + aj_bj_zeta;
    hax_lib::fstar!("Spec.Utils.is_i32b (3328*3328 + 3328*1664) $ai_bi_aj_bj");
    let o0 = montgomery_reduce_element(ai_bi_aj_bj);
    hax_lib::fstar!("calc  ( == ) {
        v $o0 % 3329;
        ( == ) { () }
        (v $ai_bi_aj_bj * 169) % 3329;
        ( == ) { assert(v $ai_bi_aj_bj == v $ai_bi + v $aj_bj_zeta) }
        ((v $ai_bi + v $aj_bj_zeta) * 169) % 3329;
        ( == ) { assert (v $aj_bj_zeta == v $aj_bj * v $zeta) }
        (((v $ai * v $bi) + (v $aj_bj * v $zeta)) * 169) % 3329;
        ( == ) { Math.Lemmas.lemma_mod_mul_distr_l ((v ai * v bi) + (v aj_bj * v zeta)) 169 3329 }
        ((((v $ai * v $bi) + (v $aj_bj * v $zeta)) % 3329) * 169) % 3329;
        ( == ) { Math.Lemmas.lemma_mod_add_distr (v ai * v bi) (v aj_bj * v zeta) 3329 }
        (((v $ai * v $bi) + ((v $aj_bj * v $zeta) % 3329)) % 3329 * 169) % 3329;
        ( == ) { Math.Lemmas.lemma_mod_mul_distr_l (v aj_bj) (v zeta) 3329 }
        (((v $ai * v $bi) + ((v $aj_bj % 3329 * v $zeta) % 3329)) % 3329 * 169) % 3329;
        ( == ) { assert(v aj_bj % 3329 == (v $aj_bj_ * 169) % 3329) }
        (((v $ai * v $bi) + (((v $aj_bj_ * 169) % 3329 * v $zeta) % 3329)) % 3329 * 169) % 3329;
        ( == ) { assert(v $aj_bj_ == v $aj * v $bj) }
        (((v $ai * v $bi) + (((v $aj * v $bj * 169) % 3329 * v $zeta) % 3329)) % 3329 * 169) % 3329;
        ( == ) { Math.Lemmas.lemma_mod_mul_distr_l (v $aj * v $bj * 169) (v $zeta) 3329 }
        (((v $ai * v $bi) + (((v $aj * v $bj * 169 * v $zeta) % 3329))) % 3329 * 169) % 3329;
        ( == ) { Math.Lemmas.lemma_mod_add_distr (v $ai * v $bi) (v $aj * v $bj * 169 * v $zeta) 3329 }
        (((v $ai * v $bi) + ((v $aj * v $bj * 169 * v $zeta))) % 3329 * 169) % 3329;
        ( == ) { Math.Lemmas.lemma_mod_mul_distr_l ((v ai * v bi) + ((v aj * v bj * 169 * v zeta))) 169 3329 }
        (((v $ai * v $bi) + ((v $aj * v $bj * 169 * v $zeta))) * 169) % 3329;
        }");
    let ai_bj = (ai as i32) * (bj as i32);
    let aj_bi = (aj as i32) * (bi as i32);
    let ai_bj_aj_bi = ai_bj + aj_bi;
    hax_lib::fstar!("Spec.Utils.is_i32b (3328*3328 + 3328*3328) ai_bj_aj_bi");
    let o1 = montgomery_reduce_element(ai_bj_aj_bi);
    hax_lib::fstar!("admit()");
    out.elements[i] = o0;
    out.elements[j] = o1;
}

// #[inline(always)]
// pub(crate) fn ntt_multiply_binomials(
//     (a0, a1): (FieldElement, FieldElement),
//     (b0, b1): (FieldElement, FieldElement),
//     zeta: FieldElementTimesMontgomeryR,
// ) -> (MontgomeryFieldElement, MontgomeryFieldElement) {
//     (
//         montgomery_reduce_element(
//             (a0 as i32) * (b0 as i32)
//                 + (montgomery_reduce_element((a1 as i32) * (b1 as i32)) as i32) * (zeta as i32),
//         ),
//         montgomery_reduce_element((a0 as i32) * (b1 as i32) + (a1 as i32) * (b0 as i32)),
//     )
// }

#[inline(always)]
pub(crate) fn ntt_multiply(
    lhs: &PortableVector,
    rhs: &PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    let mut out = zero();
    ntt_multiply_binomials(lhs, rhs, zeta0, 0, 1, &mut out);
    ntt_multiply_binomials(lhs, rhs, -zeta0, 2, 3, &mut out);
    ntt_multiply_binomials(lhs, rhs, zeta1, 4, 5, &mut out);
    ntt_multiply_binomials(lhs, rhs, -zeta1, 6, 7, &mut out);
    ntt_multiply_binomials(lhs, rhs, zeta2, 8, 9, &mut out);
    ntt_multiply_binomials(lhs, rhs, -zeta2, 10, 11, &mut out);
    ntt_multiply_binomials(lhs, rhs, zeta3, 12, 13, &mut out);
    ntt_multiply_binomials(lhs, rhs, -zeta3, 14, 15, &mut out);
    out
}
