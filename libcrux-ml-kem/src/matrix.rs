use crate::{
    hash_functions::Hash, invert_ntt::invert_ntt_montgomery, polynomial::PolynomialRingElement,
    sampling::sample_from_xof, vector::Operations,
};

#[cfg(hax)]
use hax_lib::prop::ToProp;

#[cfg(hax)]
use crate::polynomial::spec;

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
        hax_lib::loop_invariant!(|i: usize| if transpose {
            hax_lib::forall(|k: usize| {
                hax_lib::implies(
                    k < K,
                    hax_lib::forall(|l: usize| {
                        hax_lib::implies(
                            l < K,
                            if k < i {
                                spec::is_bounded_poly(3328, &A_transpose[l][k])
                            } else {
                                true.to_prop()
                            },
                        )
                    }),
                )
            })
        } else {
            hax_lib::forall(|k: usize| {
                hax_lib::implies(
                    k < K,
                    hax_lib::forall(|l: usize| {
                        hax_lib::implies(
                            l < K,
                            if k < i {
                                spec::is_bounded_poly(3328, &A_transpose[k][l])
                            } else {
                                true.to_prop()
                            },
                        )
                    }),
                )
            })
        });

        let mut seeds = [seed.clone(); K];
        for j in 0..K {
            seeds[j][32] = i as u8;
            seeds[j][33] = j as u8;
        }
        let sampled = sample_from_xof::<K, Vector, Hasher>(&seeds);
        for j in 0..K {
            hax_lib::loop_invariant!(|j: usize| if transpose {
                hax_lib::forall(|k: usize| {
                    hax_lib::implies(
                        k < K,
                        hax_lib::forall(|l: usize| {
                            hax_lib::implies(
                                l < K,
                                if k < i || (k == i && l < j) {
                                    spec::is_bounded_poly(3328, &A_transpose[l][k])
                                } else {
                                    true.to_prop()
                                },
                            )
                        }),
                    )
                })
            } else {
                hax_lib::forall(|k: usize| {
                    hax_lib::implies(
                        k < K,
                        hax_lib::forall(|l: usize| {
                            hax_lib::implies(
                                l < K,
                                if k < i || (k == i && l < j) {
                                    spec::is_bounded_poly(3328, &A_transpose[k][l])
                                } else {
                                    true.to_prop()
                                },
                            )
                        }),
                    )
                })
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
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires((K <= 4).to_prop() & (
        spec::is_bounded_poly(4095, v) & (
            hax_lib::forall(|i:usize| hax_lib::implies(i < K,
                spec::is_bounded_poly(3328, &secret_as_ntt[i]) & (
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
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires((K <= 4).to_prop() & (
        spec::is_bounded_poly(3328, message) & (
            spec::is_bounded_poly(3328, error_2) & (
                hax_lib::forall(|i:usize| hax_lib::implies(i < K,
                    spec::is_bounded_poly(3328, &t_as_ntt[i]) & (
                        spec::is_bounded_poly(3328, &r_as_ntt[i])
)))))))]
#[hax_lib::ensures(|result| spec::is_bounded_poly(3328, &result))]
pub(crate) fn compute_ring_element_v<const K: usize, Vector: Operations>(
    t_as_ntt: &[PolynomialRingElement<Vector>; K],
    r_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_2: &PolynomialRingElement<Vector>,
    message: &PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    let mut result = PolynomialRingElement::<Vector>::ZERO();

    for i in 0..K {
        hax_lib::loop_invariant!(|i: usize| spec::is_bounded_poly(i * 3328, &result));

        let product = t_as_ntt[i].ntt_multiply(&r_as_ntt[i]);
        result.add_to_ring_element(&product, i * 3328);
    }

    invert_ntt_montgomery::<K, Vector>(&mut result);
    result = error_2.add_message_error_reduce(message, result);

    result
}

/// Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires((K <= 4).to_prop() & (
        hax_lib::forall(|i:usize| hax_lib::implies(i < K,
            spec::is_bounded_poly(7, &error_1[i]) & (
                spec::is_bounded_poly(3328, &r_as_ntt[i]) & (
                    hax_lib::forall(|j:usize| hax_lib::implies(j < K,
                        spec::is_bounded_poly(3328, &a_as_ntt[i][j])))))))))]
#[hax_lib::ensures(|result| hax_lib::forall(|i:usize| hax_lib::implies(i < K,
                                spec::is_bounded_poly(3328, &result[i]))))]
pub(crate) fn compute_vector_u<const K: usize, Vector: Operations>(
    a_as_ntt: &[[PolynomialRingElement<Vector>; K]; K],
    r_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_1: &[PolynomialRingElement<Vector>; K],
) -> [PolynomialRingElement<Vector>; K] {
    let mut result = core::array::from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());

    for i in 0..K {
        hax_lib::loop_invariant!(|i: usize| hax_lib::forall(|j: usize| {
            if j < K {
                if j < i {
                    spec::is_bounded_poly(3328, &result[j])
                } else {
                    spec::is_bounded_poly(0, &result[j])
                }
            } else {
                true.to_prop()
            }
        }));

        #[cfg(hax)]
        let _result = result;

        for j in 0..K {
            hax_lib::loop_invariant!(|j: usize| spec::is_bounded_poly(j * 3328, &result[i])
                & (hax_lib::forall(|k: usize| {
                    hax_lib::implies(k < K && k != i, hax_lib::eq(&result[k], &_result[k]))
                })));

            let product = a_as_ntt[i][j].ntt_multiply(&r_as_ntt[j]);
            result[i].add_to_ring_element(&product, j * 3328);
        }
        invert_ntt_montgomery::<K, Vector>(&mut result[i]);
        result[i].add_error_reduce(&error_1[i]);
    }
    result
}

/// Compute Â ◦ ŝ + ê
#[inline(always)]
#[allow(non_snake_case)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires((K <= 4).to_prop() & (
        hax_lib::forall(|i:usize| hax_lib::implies(i < K,
            spec::is_bounded_poly(3328, &error_as_ntt[i]) & (
                spec::is_bounded_poly(3328, &s_as_ntt[i]) & (
                    hax_lib::forall(|j:usize| hax_lib::implies(j < K,
                        spec::is_bounded_poly(3328, &matrix_A[i][j])))))))))]
#[hax_lib::ensures(|result| hax_lib::forall(|i:usize| hax_lib::implies(i < K,
                                spec::is_bounded_poly(3328, &future(t_as_ntt)[i]))))]
pub(crate) fn compute_As_plus_e<const K: usize, Vector: Operations>(
    t_as_ntt: &mut [PolynomialRingElement<Vector>; K],
    matrix_A: &[[PolynomialRingElement<Vector>; K]; K],
    s_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_as_ntt: &[PolynomialRingElement<Vector>; K],
) {
    for i in 0..K {
        hax_lib::loop_invariant!(|i: usize| hax_lib::forall(|j: usize| hax_lib::implies(
            j < i,
            spec::is_bounded_poly(3328, &t_as_ntt[j])
        )));

        t_as_ntt[i] = PolynomialRingElement::<Vector>::ZERO();

        for j in 0..K {
            hax_lib::loop_invariant!(|j: usize| spec::is_bounded_poly(j * 3328, &t_as_ntt[i])
                & (hax_lib::forall(|k: usize| hax_lib::implies(
                    k < i,
                    spec::is_bounded_poly(3328, &t_as_ntt[k])
                ))));

            let product = matrix_A[i][j].ntt_multiply(&s_as_ntt[j]);
            t_as_ntt[i].add_to_ring_element(&product, j * 3328);
        }

        t_as_ntt[i].add_standard_error_reduce(&error_as_ntt[i]);
    }
}
