use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{zeta, PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    vector::{montgomery_multiply_fe, Operations},
};

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::fstar::before(
    interface,
    r#"[@@ "opaque_to_smt"]
   let ntt_re_range_2 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+5*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))"#
)]
#[hax_lib::fstar::before(
    interface,
    r#"[@@ "opaque_to_smt"]
    let ntt_re_range_1 (#v_Vector: Type0)
            {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
            (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
        forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+6*3328)
                (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))"#
)]
#[hax_lib::requires(fstar!(r#"v ${*zeta_i} == 63 /\
    ntt_re_range_2 $re"#))]
#[hax_lib::ensures(|result| fstar!(r#"ntt_re_range_1 ${re}_future /\
    v ${*zeta_i}_future == 127"#))]
pub(crate) fn ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    hax_lib::fstar!(r#"reveal_opaque (`%ntt_re_range_2) (ntt_re_range_2 #$:Vector)"#);
    hax_lib::fstar!(r#"reveal_opaque (`%ntt_re_range_1) (ntt_re_range_1 #$:Vector)"#);
    let _zeta_i_init = *zeta_i;
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            fstar!(
                r#"v zeta_i == v $_zeta_i_init + v $round * 4 /\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque (11207+5*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque (11207+6*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))"#
            )
        });
        *zeta_i += 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (11207+5*3328)
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );
        Vector::ntt_layer_1_step(
            &mut re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i + 1),
            zeta(*zeta_i + 2),
            zeta(*zeta_i + 3),
        );
        *zeta_i += 3;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (11207+6*3328)
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );
        hax_lib::fstar!(
            "assert (Spec.Utils.is_i16b_array_opaque (11207+6*3328)
        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ $round ])))"
        );
    }
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::fstar::before(
    interface,
    r#"[@@ "opaque_to_smt"]
   let ntt_re_range_3 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+4*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))"#
)]
#[hax_lib::requires(fstar!(r#"v ${*zeta_i} == 31 /\
    ntt_re_range_3 $re"#))]
#[hax_lib::ensures(|result| fstar!(r#"ntt_re_range_2 ${re}_future /\
    v ${*zeta_i}_future == 63"#))]
pub(crate) fn ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    hax_lib::fstar!(r#"reveal_opaque (`%ntt_re_range_3) (ntt_re_range_3 #$:Vector)"#);
    hax_lib::fstar!(r#"reveal_opaque (`%ntt_re_range_2) (ntt_re_range_2 #$:Vector)"#);
    let _zeta_i_init = *zeta_i;
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            fstar!(
                r#"v zeta_i == v $_zeta_i_init + v $round * 2 /\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque (11207+4*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque (11207+5*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))"#
            )
        });
        *zeta_i += 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (11207+4*3328)
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );

        Vector::ntt_layer_2_step(
            &mut re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i + 1),
        );
        *zeta_i += 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (11207+5*3328)
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );
        hax_lib::fstar!(
            "assert (Spec.Utils.is_i16b_array_opaque (11207+5*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ $round ])))"
        );
    }
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::fstar::before(
    interface,
    r#"[@@ "opaque_to_smt"]
   let ntt_re_range_4 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+3*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))"#
)]
#[hax_lib::requires(fstar!(r#"v ${*zeta_i} == 15 /\
    ntt_re_range_4 $re"#))]
#[hax_lib::ensures(|result| fstar!(r#"ntt_re_range_3 ${re}_future /\
    v ${*zeta_i}_future == 31"#))]
pub(crate) fn ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    hax_lib::fstar!(r#"reveal_opaque (`%ntt_re_range_4) (ntt_re_range_4 #$:Vector)"#);
    hax_lib::fstar!(r#"reveal_opaque (`%ntt_re_range_3) (ntt_re_range_3 #$:Vector)"#);
    let _zeta_i_init = *zeta_i;
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            fstar!(
                r#"v zeta_i == v $_zeta_i_init + v $round /\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque (11207+3*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque (11207+4*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))"#
            )
        });
        *zeta_i += 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (11207+3*3328)
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );
        Vector::ntt_layer_3_step(&mut re.coefficients[round], zeta(*zeta_i));
        hax_lib::fstar!(
            "reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
            (Spec.Utils.is_i16b_array_opaque (11207+4*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"
        );
        hax_lib::fstar!(
            "assert (Spec.Utils.is_i16b_array_opaque (11207+4*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ $round ])))"
        );
    }
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 $zeta_r /\
    (let t = ${montgomery_multiply_fe::<Vector>} $b $zeta_r in
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array $a) i) -
        v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))) /\
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array $a) i) +
        v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))))"#))]
fn ntt_layer_int_vec_step<Vector: Operations>(
    a: &mut Vector,
    b: &mut Vector,
    scratch: &mut Vector,
    zeta_r: i16,
) {
    *scratch = b.clone(); // XXX: Two copies here may not be necessary.
    montgomery_multiply_fe::<Vector>(scratch, zeta_r);
    *b = a.clone();
    Vector::add(a, scratch);
    Vector::sub(b, scratch);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"v $layer >= 4 /\ v $layer <= 7 /\
    ((v $layer == 4 ==> v ${*zeta_i} == 7) /\
    (v $layer == 5 ==> v ${*zeta_i} == 3) /\
    (v $layer == 6 ==> v ${*zeta_i} == 1) /\
    (v $layer == 7 ==> v ${*zeta_i} == 0))"#))]
#[hax_lib::ensures(|result| fstar!(r#"ntt_re_range_4 ${re}_future /\
    (v $layer == 4 ==> v ${*zeta_i}_future == 15) /\
    (v $layer == 5 ==> v ${*zeta_i}_future == 7) /\
    (v $layer == 6 ==> v ${*zeta_i}_future == 3) /\
    (v $layer == 7 ==> v ${*zeta_i}_future == 1)"#))]
pub(crate) fn ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
    scratch: &mut Vector,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    let step = 1 << layer;
    let step_vec = step / 16; //FIELD_ELEMENTS_IN_VECTOR;
    let _zeta_i_init = *zeta_i;

    // For every round, split off two `step_vec` sized slices from the front.
    let mut remaining_elements = &mut re.coefficients[..];
    for _round in 0..(128 >> layer) {
        *zeta_i += 1;

        let (a, rest) = remaining_elements.split_at_mut(step_vec);
        let (b, rest) = rest.split_at_mut(step_vec);
        remaining_elements = rest;
        for j in 0..step_vec {
            ntt_layer_int_vec_step(&mut a[j], &mut b[j], scratch, zeta(*zeta_i));
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
pub(crate) fn ntt_at_layer_7<Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
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
        *scratch = re.coefficients[j + step].clone();
        Vector::multiply_by_constant(scratch, -1600);
        re.coefficients[j + step] = re.coefficients[j];
        Vector::add(&mut re.coefficients[j], scratch);
        Vector::sub(&mut re.coefficients[j + step], scratch);
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::requires(fstar!(r#"forall i. i < 8 ==> ntt_layer_7_pre (${re}.f_coefficients.[ sz i ])
    (${re}.f_coefficients.[ sz i +! sz 8 ])"#))]
#[hax_lib::ensures(|_| fstar!(r#"Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector ${re}_future ==
    Spec.MLKEM.poly_ntt (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector $re) /\
    Libcrux_ml_kem.Serialize.coefficients_field_modulus_range #$:Vector ${re}_future"#))]
pub(crate) fn ntt_binomially_sampled_ring_element<Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.
    ntt_at_layer_7(re, scratch);

    let mut zeta_i = 1;
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, scratch, 11207);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, scratch, 11207 + 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, scratch, 11207 + 2 * 3328);
    ntt_at_layer_3(&mut zeta_i, re, 11207 + 3 * 3328);
    ntt_at_layer_2(&mut zeta_i, re, 11207 + 4 * 3328);
    ntt_at_layer_1(&mut zeta_i, re, 11207 + 5 * 3328);

    re.poly_barrett_reduce()
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::ensures(|_| fstar!(r#"Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector ${re}_future ==
    Spec.MLKEM.poly_ntt (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector $re)"#))]
pub(crate) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    ntt_at_layer_4_plus(&mut zeta_i, re, 7, scratch, 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, scratch, 2 * 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, scratch, 3 * 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, scratch, 4 * 3328);
    ntt_at_layer_3(&mut zeta_i, re, 5 * 3328);
    ntt_at_layer_2(&mut zeta_i, re, 6 * 3328);
    ntt_at_layer_1(&mut zeta_i, re, 7 * 3328);

    re.poly_barrett_reduce()
}
