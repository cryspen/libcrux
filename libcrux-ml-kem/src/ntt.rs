use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{zeta, PolynomialRingElement, VECTORS_IN_RING_ELEMENT, add_bounded, sub_bounded},
    vector::Operations,
};

#[cfg(hax)]
use crate::polynomial::spec;

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires(spec::is_bounded_poly(_initial_coefficient_bound, re).and(*zeta_i == 63 && _initial_coefficient_bound == 4803 + 5 * 3328))]
#[hax_lib::ensures(|result| spec::is_bounded_poly(_initial_coefficient_bound+3328, future(re)).and(*future(zeta_i) == 127))]
pub(crate) fn ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    let _re_init = re.clone();
    let _zeta_i_init = *zeta_i;
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            hax_lib::fstar_prop_expr!(r#"v $zeta_i == v $_zeta_i_init + v $round * 4"#).and(
            hax_lib::forall(|i: usize| {
                if i < 16 {
                    if i >= round {
                        spec::is_bounded_vector(_initial_coefficient_bound, &re.coefficients[i])
                    } else {
                        spec::is_bounded_vector(_initial_coefficient_bound + 3328, &re.coefficients[i])
                    }
                } else {
                    hax_lib::fstar_prop_expr!(r#"True"#)
                }           
            }))});
        *zeta_i += 1;
        re.coefficients[round] = Vector::ntt_layer_1_step(
            re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i + 1),
            zeta(*zeta_i + 2),
            zeta(*zeta_i + 3),
        );
        *zeta_i += 3;
    }
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires(spec::is_bounded_poly(_initial_coefficient_bound, re).and(*zeta_i == 31 && _initial_coefficient_bound == 4803 + 4 * 3328))]
#[hax_lib::ensures(|result| spec::is_bounded_poly(_initial_coefficient_bound+3328, future(re)).and(*future(zeta_i) == 63))]
pub(crate) fn ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    let _zeta_i_init = *zeta_i;
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            hax_lib::fstar_prop_expr!(r#"v $zeta_i == v $_zeta_i_init + v $round * 2"#).and(
            hax_lib::forall(|i: usize| {
                if i < 16 {
                    if i >= round {
                        spec::is_bounded_vector(_initial_coefficient_bound, &re.coefficients[i])
                    } else {
                        spec::is_bounded_vector(_initial_coefficient_bound + 3328, &re.coefficients[i])
                    }
                } else {
                    hax_lib::fstar_prop_expr!(r#"True"#)
                }           
            }))});
        *zeta_i += 1;
        
        re.coefficients[round] =
            Vector::ntt_layer_2_step(re.coefficients[round], zeta(*zeta_i), zeta(*zeta_i + 1));
        *zeta_i += 1;
    }
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires(spec::is_bounded_poly(_initial_coefficient_bound, re).and(*zeta_i == 15 && _initial_coefficient_bound == 4803 + 3 * 3328))]
#[hax_lib::ensures(|result| spec::is_bounded_poly(_initial_coefficient_bound+3328, future(re)).and(*future(zeta_i) == 31))]
pub(crate) fn ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    let _zeta_i_init = *zeta_i;
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            hax_lib::fstar_prop_expr!(r#"v $zeta_i == v $_zeta_i_init + v $round"#).and(
            hax_lib::forall(|i: usize| {
                if i < 16 {
                    if i >= round {
                        spec::is_bounded_vector(_initial_coefficient_bound, &re.coefficients[i])
                    } else {
                        spec::is_bounded_vector(_initial_coefficient_bound + 3328, &re.coefficients[i])
                    }
                } else {
                    hax_lib::fstar_prop_expr!(r#"True"#)
                }           
            }))});
        *zeta_i += 1;
        re.coefficients[round] = Vector::ntt_layer_3_step(re.coefficients[round], zeta(*zeta_i));
    }
}

#[inline(always)]
#[hax_lib::requires(spec::is_bounded_vector(_initial_coefficient_bound, &a).and(zeta_r >= -1664 && zeta_r <= 1664 && _initial_coefficient_bound <= 4803 + 3 * 3328))]
#[hax_lib::ensures(|(r0, r1)| spec::is_bounded_vector(_initial_coefficient_bound+3328, &r0).and(spec::is_bounded_vector(_initial_coefficient_bound+3328, &r1)))]
fn ntt_layer_int_vec_step<Vector: Operations>(
    mut a: Vector,
    mut b: Vector,
    zeta_r: i16,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) -> (Vector, Vector) {
    let t = Vector::montgomery_multiply_by_constant(b, zeta_r);
    b = sub_bounded(a, _initial_coefficient_bound, &t, 3328);
    a = add_bounded(a, _initial_coefficient_bound, &t, 3328);
    (a, b)
}


#[hax_lib::fstar::options("--z3rlimit 300 --ext context_pruning --split_queries always")]
#[hax_lib::requires(
    spec::is_bounded_poly(_initial_coefficient_bound, re).and(
        _initial_coefficient_bound <= 4803 + 3 * 3328 &&
        match layer {
            4 => *zeta_i == 7,
            5 => *zeta_i == 3,
            6 => *zeta_i == 1,
            7 => *zeta_i == 0,
            _ => false,
        })
)]
#[hax_lib::ensures(|result| 
    spec::is_bounded_poly(_initial_coefficient_bound+3328, future(re)).and(
        match layer {
            4 => *future(zeta_i) == 15,
            5 => *future(zeta_i) == 7,
            6 => *future(zeta_i) == 3,
            7 => *future(zeta_i) == 1,
            _ => false,
        })
)]
#[inline(always)]
pub(crate) fn ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    let step = 1 << layer;

    #[cfg(hax)]
    let _zeta_i_init = *zeta_i;
    
    for round in 0..(128 >> layer) {
        hax_lib::loop_invariant!(|round: usize| {
            hax_lib::fstar_prop_expr!(r#"v $zeta_i == v $_zeta_i_init + v $round"#).and(
            hax_lib::forall(|i: usize| {
                if i < 16 {
                    if i >= (round * step * 2) / 16 {
                        spec::is_bounded_vector(_initial_coefficient_bound, &re.coefficients[i])
                    } else {
                        spec::is_bounded_vector(_initial_coefficient_bound + 3328, &re.coefficients[i])
                    }
                } else {
                    hax_lib::fstar_prop_expr!(r#"True"#)
                }           
            }))});
        *zeta_i += 1;

        let offset = round * step * 2;
        let offset_vec = offset / 16; //FIELD_ELEMENTS_IN_VECTOR;
        let step_vec = step / 16; //FIELD_ELEMENTS_IN_VECTOR;

        for j in offset_vec..offset_vec + step_vec {
            hax_lib::loop_invariant!(|j: usize| {
                hax_lib::forall(|i: usize| {
                    if i < 16 {
                        if (i >= j && i < offset_vec + step_vec) || (i >= j + step_vec) {
                            spec::is_bounded_vector(_initial_coefficient_bound, &re.coefficients[i])
                        } else {
                            spec::is_bounded_vector(_initial_coefficient_bound + 3328, &re.coefficients[i])
                        }
                    } else {
                        hax_lib::fstar_prop_expr!(r#"True"#)
                    }           
                })});
            let (x, y) = ntt_layer_int_vec_step(
                re.coefficients[j],
                re.coefficients[j + step_vec],
                zeta(*zeta_i),
                _initial_coefficient_bound
            );
            re.coefficients[j] = x;
            re.coefficients[j + step_vec] = y;
        }
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
//We should make the loops inside this function `opaque_to_smt` to get it work
#[hax_lib::fstar::before(
    interface,
    r#"[@@ "opaque_to_smt"]
   let ntt_layer_7_pre (#v_Vector: Type0)
        {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
        (re_0 re_1: v_Vector) =
    (forall i. i < 16 ==>
      Spec.Utils.is_intb (pow2 15 - 1)
      (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array re_1) i) * v ((mk_i16 (-1600))))) /\
    (let t = Libcrux_ml_kem.Vector.Traits.f_multiply_by_constant re_1 ((mk_i16 (-1600))) in
    (forall i. i < 16 ==> 
      Spec.Utils.is_intb (pow2 15 - 1) 
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array re_0) i) - 
          v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))) /\
    (forall i. i < 16 ==> 
      Spec.Utils.is_intb (pow2 15 - 1) 
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array re_0) i) + 
          v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))))"#
)]
#[hax_lib::requires(fstar!(r#"forall i. i < 8 ==> ntt_layer_7_pre (${re}.f_coefficients.[ sz i ])
    (${re}.f_coefficients.[ sz i +! sz 8 ])"#))]

#[hax_lib::fstar::options("--z3rlimit 300 --ext context_pruning --split_queries always")]
#[hax_lib::requires(
    spec::is_bounded_poly(_initial_coefficient_bound, re).and(
        _initial_coefficient_bound <= 4803 + 3 * 3328 &&
        match layer {
            4 => *zeta_i == 7,
            5 => *zeta_i == 3,
            6 => *zeta_i == 1,
            7 => *zeta_i == 0,
            _ => false,
        })
)]
#[hax_lib::ensures(|result| 
    spec::is_bounded_poly(_initial_coefficient_bound+3328, future(re)).and(
        match layer {
            4 => *future(zeta_i) == 15,
            5 => *future(zeta_i) == 7,
            6 => *future(zeta_i) == 3,
            7 => *future(zeta_i) == 1,
            _ => false,
        })
)]
pub(crate) fn ntt_at_layer_7<Vector: Operations>(re: &mut PolynomialRingElement<Vector>) {
    let step = VECTORS_IN_RING_ELEMENT / 2;
    hax_lib::fstar!(r#"assert (v $step == 8)"#);
    for j in 0..step {
        hax_lib::loop_invariant!(|j: usize| {
            fstar!(
                r#"(v j < 8 ==>
          (forall (i:nat). (i >= v j /\ i < 8) ==>
            ntt_layer_7_pre (re.f_coefficients.[ sz i ]) (re.f_coefficients.[ sz i +! sz 8 ])))"#
            )
        });
        hax_lib::fstar!(r#"reveal_opaque (`%ntt_layer_7_pre) (ntt_layer_7_pre #$:Vector)"#);
        let t = Vector::multiply_by_constant(re.coefficients[j + step], -1600);
        re.coefficients[j + step] = Vector::sub(re.coefficients[j], &t);
        re.coefficients[j] = Vector::add(re.coefficients[j], &t);
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::requires(fstar!(r#"forall i. i < 8 ==> ntt_layer_7_pre (${re}.f_coefficients.[ sz i ])
    (${re}.f_coefficients.[ sz i +! sz 8 ])"#))]
#[hax_lib::ensures(|_| fstar!(r#"Libcrux_ml_kem.Polynomial.is_bounded_poly 3328 ${re}_future /\
    Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector ${re}_future ==
    Spec.MLKEM.poly_ntt (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector $re) /\
    Libcrux_ml_kem.Polynomial.is_bounded_poly #$:Vector 3328 ${re}_future"#))]
pub(crate) fn ntt_binomially_sampled_ring_element<Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
) {
    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.
    ntt_at_layer_7(re);

    let mut zeta_i = 1;
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, 4803);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, 4803 + 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, 4803 + 2 * 3328);
    ntt_at_layer_3(&mut zeta_i, re, 4803 + 3 * 3328);
    ntt_at_layer_2(&mut zeta_i, re, 4803 + 4 * 3328);
    ntt_at_layer_1(&mut zeta_i, re, 4803 + 5 * 3328);

    re.poly_barrett_reduce()
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::ensures(|_| fstar!(r#"Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector ${re}_future ==
    Spec.MLKEM.poly_ntt (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector $re)"#))]
pub(crate) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    ntt_at_layer_4_plus(&mut zeta_i, re, 7, 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, 2 * 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, 3 * 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, 4 * 3328);
    ntt_at_layer_3(&mut zeta_i, re, 5 * 3328);
    ntt_at_layer_2(&mut zeta_i, re, 6 * 3328);
    ntt_at_layer_1(&mut zeta_i, re, 7 * 3328);

    re.poly_barrett_reduce()
}
