use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{PolynomialRingElement, VECTORS_IN_RING_ELEMENT, get_zeta},
    vector::{montgomery_multiply_fe, Operations},
};

#[inline(always)]
#[hax_lib::fstar::before(interface, "[@@ \"opaque_to_smt\"]
   let ntt_re_range_2 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+5*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))")]
#[hax_lib::fstar::before(interface, "[@@ \"opaque_to_smt\"]
    let ntt_re_range_1 (#v_Vector: Type0)
            {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
            (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
        forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+6*3328)
                (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))")]
#[hax_lib::requires(fstar!("v ${*zeta_i} == 63 /\\
    ntt_re_range_2 $re"))]
#[hax_lib::ensures(|result| fstar!("ntt_re_range_1 ${re}_future /\\
    v ${*zeta_i}_future == 127"))]
pub(crate) fn ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    hax_lib::fstar!("reveal_opaque (`%ntt_re_range_2) (ntt_re_range_2 #$:Vector)");
    hax_lib::fstar!("reveal_opaque (`%ntt_re_range_1) (ntt_re_range_1 #$:Vector)");
    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init + v $round * 4 /\\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque (11207+5*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque (11207+6*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))") });
        *zeta_i += 1;
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (11207+5*3328)
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))");
        re.coefficients[round] = Vector::ntt_layer_1_step(
            re.coefficients[round],
            get_zeta (*zeta_i),
            get_zeta (*zeta_i + 1),
            get_zeta (*zeta_i + 2),
            get_zeta (*zeta_i + 3),
        );
        *zeta_i += 3;
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (11207+6*3328)
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))");
        hax_lib::fstar!("assert (Spec.Utils.is_i16b_array_opaque (11207+6*3328)
        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ $round ])))");
    }
    ()
}

#[inline(always)]
#[hax_lib::fstar::before(interface, "[@@ \"opaque_to_smt\"]
   let ntt_re_range_3 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+4*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))")]
#[hax_lib::requires(fstar!("v ${*zeta_i} == 31 /\\
    ntt_re_range_3 $re"))]
#[hax_lib::ensures(|result| fstar!("ntt_re_range_2 ${re}_future /\\
    v ${*zeta_i}_future == 63"))]
pub(crate) fn ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    hax_lib::fstar!("reveal_opaque (`%ntt_re_range_3) (ntt_re_range_3 #$:Vector)");
    hax_lib::fstar!("reveal_opaque (`%ntt_re_range_2) (ntt_re_range_2 #$:Vector)");
    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init + v $round * 2 /\\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque (11207+4*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque (11207+5*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))") });
        *zeta_i += 1;
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (11207+4*3328)
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))");
        re.coefficients[round] = Vector::ntt_layer_2_step(
            re.coefficients[round],
            get_zeta (*zeta_i),
            get_zeta (*zeta_i + 1),
        );
        *zeta_i += 1;
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (11207+5*3328)
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))");
        hax_lib::fstar!("assert (Spec.Utils.is_i16b_array_opaque (11207+5*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ $round ])))");
    }
    ()
}

#[inline(always)]
#[hax_lib::fstar::before(interface, "[@@ \"opaque_to_smt\"]
   let ntt_re_range_4 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+3*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))")]
#[hax_lib::requires(fstar!("v ${*zeta_i} == 15 /\\
    ntt_re_range_4 $re"))]
#[hax_lib::ensures(|result| fstar!("ntt_re_range_3 ${re}_future /\\
    v ${*zeta_i}_future == 31"))]
pub(crate) fn ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    hax_lib::fstar!("reveal_opaque (`%ntt_re_range_4) (ntt_re_range_4 #$:Vector)");
    hax_lib::fstar!("reveal_opaque (`%ntt_re_range_3) (ntt_re_range_3 #$:Vector)");
    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init + v $round /\\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque (11207+3*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque (11207+4*3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))") });
        *zeta_i += 1;
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (11207+3*3328)
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))");
        re.coefficients[round] =
            Vector::ntt_layer_3_step(re.coefficients[round], get_zeta (*zeta_i));
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
            (Spec.Utils.is_i16b_array_opaque (11207+4*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))");
        hax_lib::fstar!("assert (Spec.Utils.is_i16b_array_opaque (11207+4*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ $round ])))");
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(fstar!("Spec.Utils.is_i16b 1664 $zeta_r /\\
    (let t = ${montgomery_multiply_fe::<Vector>} $b $zeta_r in
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array $a) i) -
        v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))) /\\
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array $a) i) +
        v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))))"))]
fn ntt_layer_int_vec_step<Vector: Operations>(
    mut a: Vector,
    mut b: Vector,
    zeta_r: i16,
) -> (Vector, Vector) {
    let t = montgomery_multiply_fe::<Vector>(b, zeta_r);
    b = Vector::sub(a, &t);
    a = Vector::add(a, &t);
    (a, b)
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!("v $layer >= 4 /\\ v $layer <= 7 /\\
    ((v $layer == 4 ==> v ${*zeta_i} == 7) /\\
    (v $layer == 5 ==> v ${*zeta_i} == 3) /\\
    (v $layer == 6 ==> v ${*zeta_i} == 1) /\\
    (v $layer == 7 ==> v ${*zeta_i} == 0))"))]
#[hax_lib::ensures(|result| fstar!("ntt_re_range_4 ${re}_future /\\
    (v $layer == 4 ==> v ${*zeta_i}_future == 15) /\\
    (v $layer == 5 ==> v ${*zeta_i}_future == 7) /\\
    (v $layer == 6 ==> v ${*zeta_i}_future == 3) /\\
    (v $layer == 7 ==> v ${*zeta_i}_future == 1)"))]
pub(crate) fn ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
    _initial_coefficient_bound: usize,
) {
    let step = 1 << layer;

    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..(128 >> layer) {
        *zeta_i += 1;

        let offset = round * step * 2;
        let offset_vec = offset / 16; //FIELD_ELEMENTS_IN_VECTOR;
        let step_vec = step / 16; //FIELD_ELEMENTS_IN_VECTOR;

        for j in offset_vec..offset_vec + step_vec {
            let (x, y) = ntt_layer_int_vec_step(
                re.coefficients[j],
                re.coefficients[j + step_vec],
                get_zeta (*zeta_i),
            );
            re.coefficients[j] = x;
            re.coefficients[j + step_vec] = y;
        }
    }
    ()
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
//We should make the loops inside this function `opaque_to_smt` to get it work
#[hax_lib::fstar::before(interface, "[@@ \"opaque_to_smt\"]
   let ntt_layer_7_pre (#v_Vector: Type0)
        {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
        (re_0 re_1: v_Vector) =
    (forall i. i < 16 ==>
      Spec.Utils.is_intb (pow2 15 - 1)
      (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array re_1) i) * v (-1600s))) /\\
    (let t = Libcrux_ml_kem.Vector.Traits.f_multiply_by_constant re_1 (-1600s) in
    (forall i. i < 16 ==> 
      Spec.Utils.is_intb (pow2 15 - 1) 
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array re_0) i) - 
          v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))) /\\
    (forall i. i < 16 ==> 
      Spec.Utils.is_intb (pow2 15 - 1) 
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array re_0) i) + 
          v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))))")]
#[hax_lib::requires(fstar!("forall i. i < 8 ==> ntt_layer_7_pre (${re}.f_coefficients.[ sz i ])
    (${re}.f_coefficients.[ sz i +! sz 8 ])"))]
pub(crate) fn ntt_at_layer_7<Vector: Operations>(re: &mut PolynomialRingElement<Vector>) {
    let step = VECTORS_IN_RING_ELEMENT / 2;
    hax_lib::fstar!("assert (v $step == 8)");
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for j in 0..step {
        hax_lib::loop_invariant!(|j: usize| { fstar!("(v j < 8 ==>
          (forall (i:nat). (i >= v j /\\ i < 8) ==>
            ntt_layer_7_pre (re.f_coefficients.[ sz i ]) (re.f_coefficients.[ sz i +! sz 8 ])))") });
        hax_lib::fstar!("reveal_opaque (`%ntt_layer_7_pre) (ntt_layer_7_pre #$:Vector)");
        let t = Vector::multiply_by_constant(re.coefficients[j + step], -1600);
        re.coefficients[j + step] = Vector::sub(re.coefficients[j], &t);
        re.coefficients[j] = Vector::add(re.coefficients[j], &t);
    }
    ()
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::requires(fstar!("forall i. i < 8 ==> ntt_layer_7_pre (${re}.f_coefficients.[ sz i ])
    (${re}.f_coefficients.[ sz i +! sz 8 ])"))]
pub(crate) fn ntt_binomially_sampled_ring_element<Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
) {
    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.
    ntt_at_layer_7(re);

    let mut zeta_i = 1;
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, 11207);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, 11207+3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, 11207+2*3328);
    ntt_at_layer_3(&mut zeta_i, re, 3, 11207+3*3328);
    ntt_at_layer_2(&mut zeta_i, re, 2, 11207+4*3328);
    ntt_at_layer_1(&mut zeta_i, re, 1, 11207+5*3328);

    re.poly_barrett_reduce()
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200")]
pub(crate) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    ntt_at_layer_4_plus(&mut zeta_i, re, 7, 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, 2*3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, 3*3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, 4*3328);
    ntt_at_layer_3(&mut zeta_i, re, 3, 5*3328);
    ntt_at_layer_2(&mut zeta_i, re, 2, 6*3328);
    ntt_at_layer_1(&mut zeta_i, re, 1, 7*3328);

    re.poly_barrett_reduce()
}
