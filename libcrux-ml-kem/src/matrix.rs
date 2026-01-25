use crate::{
    hash_functions::Hash, helper::cloop, invert_ntt::invert_ntt_montgomery,
    polynomial::{spec, PolynomialRingElement}, sampling::sample_from_xof, vector::Operations,
};

#[cfg(hax)]
use hax_lib::prop::ToProp;

#[inline(always)]
#[allow(non_snake_case)]
#[hax_lib::fstar::options("--z3rlimit 400 --ext context_pruning")]
#[hax_lib::requires(K <= 4)]
#[hax_lib::ensures(|res| hax_lib::forall(|i:usize| hax_lib::implies(i < K,
                            hax_lib::forall(|j:usize| hax_lib::implies(j < K, 
                                spec::is_bounded_poly(3328, &(future(A_transpose)[i][j])))))))]
pub(crate) fn sample_matrix_A<const K: usize, Vector: Operations, Hasher: Hash<K>>(
    A_transpose: &mut [[PolynomialRingElement<Vector>; K]; K],
    seed: &[u8; 34],
    transpose: bool,
) {
    for i in 0..K {
        hax_lib::loop_invariant!(|i: usize| 
            if transpose {
                hax_lib::forall(|k: usize| hax_lib::implies(k < K,
                    hax_lib::forall(|l: usize| hax_lib::implies(l < K,
                        if k < i {
                            spec::is_bounded_poly(3328, &A_transpose[l][k])
                        } else {
                            true.to_prop()
                        }
                    ))))
            } else {
                hax_lib::forall(|k: usize| hax_lib::implies(k < K,
                    hax_lib::forall(|l: usize| hax_lib::implies(l < K,
                        if k < i {
                            spec::is_bounded_poly(3328, &A_transpose[k][l])
                        } else {
                            true.to_prop()
                        }
                    ))))
            }
        );

        let mut seeds = [seed.clone(); K];
        for j in 0..K {
            seeds[j][32] = i as u8;
            seeds[j][33] = j as u8;
        }
        let sampled = sample_from_xof::<K, Vector, Hasher>(&seeds);
        for j in 0..K {
            hax_lib::loop_invariant!(|j: usize| 
                if transpose {
                    hax_lib::forall(|k: usize| hax_lib::implies(k < K,
                        hax_lib::forall(|l: usize| hax_lib::implies(l < K,
                            if k < i || (k == i && l < j) {
                                spec::is_bounded_poly(3328, &A_transpose[l][k])
                            } else {
                                true.to_prop()
                            }
                        ))))
                }
                else {
                    hax_lib::forall(|k: usize| hax_lib::implies(k < K,
                        hax_lib::forall(|l: usize| hax_lib::implies(l < K,
                            if k < i || (k == i && l < j) {
                                spec::is_bounded_poly(3328, &A_transpose[k][l])
                            } else {
                                true.to_prop()
                            }
                        ))))
                });
            // A[i][j] = A_transpose[j][i]
            if transpose {
                A_transpose[j][i] = sampled[j];
            } else {
                A_transpose[i][j] = sampled[j];
            }
        }
    }
}

/// The following functions compute various expressions involving
/// vectors and matrices. The computation of these expressions has been
/// abstracted away into these functions in order to save on loop iterations.

/// Compute v − InverseNTT(sᵀ ◦ NTT(u))
#[inline(always)]
#[hax_lib::requires((K <= 4).to_prop().and(
        spec::is_bounded_poly(4095, v).and(
            hax_lib::forall(|i:usize| hax_lib::implies(i < K,
                spec::is_bounded_poly(3328, &secret_as_ntt[i]).and(
                    spec::is_bounded_poly(3328, &u_as_ntt[i])
))))))]
#[hax_lib::ensures(|result| spec::is_bounded_poly(3328, &result))]
pub(crate) fn compute_message<const K: usize, Vector: Operations>(
    v: &PolynomialRingElement<Vector>,
    secret_as_ntt: &[PolynomialRingElement<Vector>; K],
    u_as_ntt: &[PolynomialRingElement<Vector>; K],
) -> PolynomialRingElement<Vector> {
    let mut result = PolynomialRingElement::<Vector>::ZERO();

    hax_lib::assert_prop!(spec::is_bounded_poly(0, &result));

    for i in 0..K {
        hax_lib::loop_invariant!(|i: usize| spec::is_bounded_poly(i * 3328, &result));
        
        let product = secret_as_ntt[i].ntt_multiply(&u_as_ntt[i]);
        result.add_to_ring_element(&product, i * 3328);
    }

    invert_ntt_montgomery::<K, Vector>(&mut result);
    result = v.subtract_reduce(result);

    result
}

/// Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K"#))]
#[hax_lib::ensures(|res|
    fstar!(r#"let open Libcrux_ml_kem.Vector in
        let tt_spec = to_spec_vector_t $t_as_ntt in
        let r_spec = to_spec_vector_t $r_as_ntt in
        let e2_spec = to_spec_poly_t $error_2 in
        let m_spec = to_spec_poly_t $message in
        let res_spec = to_spec_poly_t $res in
        res_spec == Spec.MLKEM.(poly_add (poly_add (vector_dot_product_ntt #$K tt_spec r_spec) e2_spec) m_spec) /\
        Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly (sz 3328) $res"#)
)]
pub(crate) fn compute_ring_element_v<const K: usize, Vector: Operations>(
    t_as_ntt: &[PolynomialRingElement<Vector>; K],
    r_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_2: &PolynomialRingElement<Vector>,
    message: &PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    let mut result = PolynomialRingElement::<Vector>::ZERO();

    for i in 0..K {
        let product = t_as_ntt[i].ntt_multiply(&r_as_ntt[i]);
        result.add_to_ring_element(&product, i * 3328);
    }

    invert_ntt_montgomery::<K, Vector>(&mut result);
    result = error_2.add_message_error_reduce(message, result);

    result
}

/// Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"
    Spec.MLKEM.is_rank $K /\
    (forall (i:nat). i < v $K ==>
        Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly (sz 7) (Seq.index ${error_1} i))"#))]
#[hax_lib::ensures(|res|
    fstar!(r#"let open Libcrux_ml_kem.Vector in
        let a_spec = to_spec_matrix_t $a_as_ntt in
        let r_spec = to_spec_vector_t $r_as_ntt in
        let e_spec = to_spec_vector_t $error_1 in
        let res_spec = to_spec_vector_t $res in
        res_spec == Spec.MLKEM.(vector_add (vector_inv_ntt (matrix_vector_mul_ntt a_spec r_spec)) e_spec) /\
        (forall (i:nat). i < v $K ==>
            Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly (sz 3328) (Seq.index $res i))"#)
)]
pub(crate) fn compute_vector_u<const K: usize, Vector: Operations>(
    a_as_ntt: &[[PolynomialRingElement<Vector>; K]; K],
    r_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_1: &[PolynomialRingElement<Vector>; K],
) -> [PolynomialRingElement<Vector>; K] {
    let mut result = core::array::from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());

    cloop! {
        for (i, row) in a_as_ntt.iter().enumerate() {
            cloop! {
                for (j, a_element) in row.iter().enumerate() {
                    let product = a_element.ntt_multiply(&r_as_ntt[j]);
                    result[i].add_to_ring_element(&product, j * 3328);
                }
            }

            invert_ntt_montgomery::<K, Vector>(&mut result[i]);
            result[i].add_error_reduce(&error_1[i]);
        }
    }

    result
}

/// Compute Â ◦ ŝ + ê
#[inline(always)]
#[allow(non_snake_case)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K"#))]
#[hax_lib::ensures(|res|
    fstar!(r#"let open Libcrux_ml_kem.Vector in
        to_spec_vector_t ${t_as_ntt}_future =
             Spec.MLKEM.compute_As_plus_e_ntt
               (to_spec_matrix_t $matrix_A) 
               (to_spec_vector_t $s_as_ntt) 
               (to_spec_vector_t $error_as_ntt) /\
        (forall (i: nat). i < v $K ==>
            Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly (sz 3328) (Seq.index ${t_as_ntt}_future i))"#)
)]
pub(crate) fn compute_As_plus_e<const K: usize, Vector: Operations>(
    t_as_ntt: &mut [PolynomialRingElement<Vector>; K],
    matrix_A: &[[PolynomialRingElement<Vector>; K]; K],
    s_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_as_ntt: &[PolynomialRingElement<Vector>; K],
) {
    cloop! {
        for (i, row) in matrix_A.iter().enumerate() {
            // This may be externally provided memory. Ensure that `t_as_ntt`
            // is all 0.
            t_as_ntt[i] = PolynomialRingElement::<Vector>::ZERO();
            cloop! {
                for (j, matrix_element) in row.iter().enumerate() {
                    let product = matrix_element.ntt_multiply(&s_as_ntt[j]);
                    t_as_ntt[i].add_to_ring_element(&product, j * 3328);
                }
            }
            t_as_ntt[i].add_standard_error_reduce(&error_as_ntt[i]);
        }
    };
    ()
}
