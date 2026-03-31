use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{add_bounded, sub_bounded, zeta},
    vector::{Operations, PolynomialRingElement, FIELD_ELEMENTS_IN_VECTOR},
};

#[cfg(hax)]
use hax_lib::prop::ToProp;

#[cfg(hax)]
use crate::polynomial::spec;

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires(spec::is_bounded_poly(4 * 3328, re) & (*zeta_i == 128))]
#[hax_lib::ensures(|result| spec::is_bounded_poly(3328, future(re)) & (*future(zeta_i) == 64))]
pub(crate) fn invert_ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
) {
    #[cfg(hax)]
    let _zeta_i_init = *zeta_i;

    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            (*zeta_i == _zeta_i_init - round * 4).to_prop()
                & (hax_lib::forall(|i: usize| {
                    if i < 16 {
                        if i >= round {
                            spec::is_bounded_vector(4 * 3328, &re.coefficients[i])
                        } else {
                            spec::is_bounded_vector(3328, &re.coefficients[i])
                        }
                    } else {
                        true.to_prop()
                    }
                }))
        });

        *zeta_i -= 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (4*3328) 
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );
        re.coefficients[round] = Vector::inv_ntt_layer_1_step(
            re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i - 1),
            zeta(*zeta_i - 2),
            zeta(*zeta_i - 3),
        );
        *zeta_i -= 3;
    }
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires(spec::is_bounded_poly(3328, re) & (*zeta_i == 64))]
#[hax_lib::ensures(|result| spec::is_bounded_poly(3328, future(re)) & (*future(zeta_i) == 32))]
pub(crate) fn invert_ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
) {
    #[cfg(hax)]
    let _zeta_i_init = *zeta_i;

    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            (*zeta_i == _zeta_i_init - round * 2).to_prop()
                & (hax_lib::forall(|i: usize| {
                    if i < 16 {
                        if i >= round {
                            spec::is_bounded_vector(3328, &re.coefficients[i])
                        } else {
                            spec::is_bounded_vector(3328, &re.coefficients[i])
                        }
                    } else {
                        true.to_prop()
                    }
                }))
        });

        *zeta_i -= 1;
        re.coefficients[round] =
            Vector::inv_ntt_layer_2_step(re.coefficients[round], zeta(*zeta_i), zeta(*zeta_i - 1));
        *zeta_i -= 1;
    }
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires(spec::is_bounded_poly(3328, re) & (*zeta_i == 32))]
#[hax_lib::ensures(|result| spec::is_bounded_poly(3328, future(re)) & (*future(zeta_i) == 16))]
pub(crate) fn invert_ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
) {
    #[cfg(hax)]
    let _zeta_i_init = *zeta_i;

    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            (*zeta_i == _zeta_i_init - round).to_prop()
                & (hax_lib::forall(|i: usize| {
                    if i < 16 {
                        if i >= round {
                            spec::is_bounded_vector(3328, &re.coefficients[i])
                        } else {
                            spec::is_bounded_vector(3328, &re.coefficients[i])
                        }
                    } else {
                        true.to_prop()
                    }
                }))
        });

        *zeta_i -= 1;

        re.coefficients[round] =
            Vector::inv_ntt_layer_3_step(re.coefficients[round], zeta(*zeta_i));
    }
}

#[inline(always)]
#[hax_lib::requires(spec::is_bounded_vector(3328, &a) & (spec::is_bounded_vector(3328, &b) & (zeta_r >= -1664 && zeta_r <= 1664)))]
#[hax_lib::ensures(|(r0, r1)| spec::is_bounded_vector(3328, &r0) & (spec::is_bounded_vector(3328, &r1)))]
pub(crate) fn inv_ntt_layer_int_vec_step_reduce<Vector: Operations>(
    mut a: Vector,
    mut b: Vector,
    zeta_r: i16,
) -> (Vector, Vector) {
    let b_minus_a = sub_bounded(b, 3328, &a, 3328);
    let a_plus_b = add_bounded(a, 3328, &b, 3328);

    #[cfg(hax)]
    spec::is_bounded_vector_higher(&a_plus_b, 6656, 28296);

    a = Vector::barrett_reduce(a_plus_b);
    b = Vector::montgomery_multiply_by_constant(b_minus_a, zeta_r);
    (a, b)
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires(
    spec::is_bounded_poly(3328, re) & (
        match layer {
            4 => *zeta_i == 16,
            5 => *zeta_i == 8,
            6 => *zeta_i == 4,
            7 => *zeta_i == 2,
            _ => false,
        })
)]
#[hax_lib::ensures(|result| spec::is_bounded_poly(3328, future(re)) & (
        match layer {
            4 => *future(zeta_i) == 8,
            5 => *future(zeta_i) == 4,
            6 => *future(zeta_i) == 2,
            7 => *future(zeta_i) == 1,
            _ => false,
        })
)]
pub(crate) fn invert_ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
) {
    #[cfg(hax)]
    let _zeta_i_init = *zeta_i;

    let step = 1 << layer;

    for round in 0..(128 >> layer) {
        hax_lib::loop_invariant!(|round: usize| {
            (*zeta_i == _zeta_i_init - round).to_prop()
                & (hax_lib::forall(|i: usize| {
                    if i < 16 {
                        if i >= (round * step * 2) / 16 {
                            spec::is_bounded_vector(3328, &re.coefficients[i])
                        } else {
                            spec::is_bounded_vector(3328, &re.coefficients[i])
                        }
                    } else {
                        true.to_prop()
                    }
                }))
        });

        *zeta_i -= 1;

        let offset = round * step * 2;
        let offset_vec = offset / FIELD_ELEMENTS_IN_VECTOR;
        let step_vec = step / FIELD_ELEMENTS_IN_VECTOR;

        for j in offset_vec..offset_vec + step_vec {
            hax_lib::loop_invariant!(|j: usize| {
                hax_lib::forall(|i: usize| {
                    if i < 16 {
                        if (i >= j && i < offset_vec + step_vec) || (i >= j + step_vec) {
                            spec::is_bounded_vector(3328, &re.coefficients[i])
                        } else {
                            spec::is_bounded_vector(3328, &re.coefficients[i])
                        }
                    } else {
                        true.to_prop()
                    }
                })
            });

            let (x, y) = inv_ntt_layer_int_vec_step_reduce(
                re.coefficients[j],
                re.coefficients[j + step_vec],
                zeta(*zeta_i),
            );
            re.coefficients[j] = x;
            re.coefficients[j + step_vec] = y;
        }
    }
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires((K <= 4).to_prop() & (spec::is_bounded_poly(K * 3328, re)))]
#[hax_lib::ensures(|result| spec::is_bounded_poly(3328, future(re)))]
pub(crate) fn invert_ntt_montgomery<const K: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
) {
    // We only ever call this function after matrix/vector multiplication
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() <= (K as i16) * 3328));

    #[cfg(hax)]
    spec::is_bounded_poly_higher(re, K * 3328, 4 * 3328);

    let mut zeta_i = super::constants::COEFFICIENTS_IN_RING_ELEMENT / 2;

    invert_ntt_at_layer_1(&mut zeta_i, re);
    invert_ntt_at_layer_2(&mut zeta_i, re);
    invert_ntt_at_layer_3(&mut zeta_i, re);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 4);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 5);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 6);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 7);
}
