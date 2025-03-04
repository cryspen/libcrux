use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{zeta, PolynomialRingElement},
    vector::{montgomery_multiply_fe, Operations, FIELD_ELEMENTS_IN_VECTOR},
};

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::fstar::before(
    interface,
    "[@@ \"opaque_to_smt\"]
   let invert_ntt_re_range_2 (#v_Vector: Type0)
           {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
           (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque 3328
               (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))"
)]
#[hax_lib::fstar::before(
    interface,
    "[@@ \"opaque_to_smt\"]
   let invert_ntt_re_range_1 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (4 * 3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))"
)]
#[hax_lib::requires(fstar!(r#"v ${*zeta_i} == 128 /\
    invert_ntt_re_range_1 $re"#))]
#[hax_lib::ensures(|result| fstar!(r#"invert_ntt_re_range_2 ${re}_future /\
    v ${*zeta_i}_future == 64"#))]
pub(crate) fn invert_ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(r#"reveal_opaque (`%invert_ntt_re_range_1) (invert_ntt_re_range_1 #$:Vector)"#);
    hax_lib::fstar!(r#"reveal_opaque (`%invert_ntt_re_range_2) (invert_ntt_re_range_2 #$:Vector)"#);
    let _zeta_i_init = *zeta_i;
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            fstar!(
                r#"v zeta_i == v $_zeta_i_init - v $round * 4 /\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque (4 * 3328)
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque 3328
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))"#
            )
        });
        *zeta_i -= 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (4*3328) 
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );
        Vector::inv_ntt_layer_1_step(
            &mut re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i - 1),
            zeta(*zeta_i - 2),
            zeta(*zeta_i - 3),
        );
        *zeta_i -= 3;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328 
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );
        hax_lib::fstar!(
            "assert (Spec.Utils.is_i16b_array_opaque 3328
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ $round ])))"
        );
    }
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires(fstar!(r#"v ${*zeta_i} == 64 /\
    invert_ntt_re_range_2 $re "#))]
#[hax_lib::ensures(|result| fstar!(r#"invert_ntt_re_range_2 ${re}_future /\
    v ${*zeta_i}_future == 32"#))]
pub(crate) fn invert_ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(r#"reveal_opaque (`%invert_ntt_re_range_2) (invert_ntt_re_range_2 #$:Vector)"#);
    let _zeta_i_init = *zeta_i;
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            fstar!(
                r#"v zeta_i == v $_zeta_i_init - v $round * 2 /\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque 3328
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque 3328
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))"#
            )
        });
        *zeta_i -= 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328 
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );

        Vector::inv_ntt_layer_2_step(
            &mut re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i - 1),
        );
        *zeta_i -= 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328 
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );
        hax_lib::fstar!(
            "assert (Spec.Utils.is_i16b_array_opaque 3328
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ $round ])))"
        );
    }
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[hax_lib::requires(fstar!(r#"v ${*zeta_i} == 32 /\
    invert_ntt_re_range_2 $re"#))]
#[hax_lib::ensures(|result| fstar!(r#"invert_ntt_re_range_2 ${re}_future /\
    v ${*zeta_i}_future == 16"#))]
pub(crate) fn invert_ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(r#"reveal_opaque (`%invert_ntt_re_range_2) (invert_ntt_re_range_2 #$:Vector)"#);
    let _zeta_i_init = *zeta_i;
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            fstar!(
                r#"v zeta_i == v $_zeta_i_init - v $round /\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque 3328
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque 3328
              (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))"#
            )
        });
        *zeta_i -= 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328 
                        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"#
        );
        Vector::inv_ntt_layer_3_step(&mut re.coefficients[round], zeta(*zeta_i));
        hax_lib::fstar!(
            "reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
            (Spec.Utils.is_i16b_array_opaque 3328 
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))"
        );
        hax_lib::fstar!(
            "assert (Spec.Utils.is_i16b_array_opaque 3328
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ $round ])))"
        );
    }
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 $zeta_r /\
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array $b) i) -
        v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array $a) i))) /\
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array $a) i) +
        v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array $b) i))) /\
    Spec.Utils.is_i16b_array 28296 (Libcrux_ml_kem.Vector.Traits.f_to_i16_array
        (Libcrux_ml_kem.Vector.Traits.f_add $a $b))"#))]
pub(crate) fn inv_ntt_layer_int_vec_step_reduce<Vector: Operations>(
    a: &mut Vector,
    b: &mut Vector,
    scratch: &mut Vector,
    zeta_r: i16,
) {
    *scratch = b.clone();
    Vector::sub(scratch, &a);
    Vector::add(a, b);
    Vector::barrett_reduce(a);
    montgomery_multiply_fe::<Vector>(scratch, zeta_r);
    *b = scratch.clone();
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"v $layer >= 4 /\ v $layer <= 7"#))]
pub(crate) fn invert_ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
    scratch: &mut Vector,
) {
    let step = 1 << layer;
    let step_vec = step / FIELD_ELEMENTS_IN_VECTOR;

    // For every round, split off two `step_vec` sized slices from the front.
    let mut remaining_elements = &mut re.coefficients[..];
    for _round in 0..(128 >> layer) {
        *zeta_i -= 1;

        // XXX: split_at_mut this
        let (a, rest) = remaining_elements.split_at_mut(step_vec);
        let (b, rest) = rest.split_at_mut(step_vec);
        remaining_elements = rest;
        for j in 0..step_vec {
            inv_ntt_layer_int_vec_step_reduce(&mut a[j], &mut b[j], scratch, zeta(*zeta_i));
        }
    }
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"invert_ntt_re_range_1 $re"#))]
pub(crate) fn invert_ntt_montgomery<const K: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
    // We only ever call this function after matrix/vector multiplication
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() < (K as i16) * FIELD_MODULUS));

    let mut zeta_i = super::constants::COEFFICIENTS_IN_RING_ELEMENT / 2;

    invert_ntt_at_layer_1(&mut zeta_i, re);
    invert_ntt_at_layer_2(&mut zeta_i, re);
    invert_ntt_at_layer_3(&mut zeta_i, re);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 4, scratch);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 5, scratch);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 6, scratch);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 7, scratch);

    hax_debug_assert!(
        to_i16_array(re)[0].abs() < 128 * (K as i16) * FIELD_MODULUS
            && to_i16_array(re)[1].abs() < 128 * (K as i16) * FIELD_MODULUS
    );
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .enumerate()
        .skip(2)
        .all(|(i, coefficient)| coefficient.abs() < (128 / (1 << i.ilog2())) * FIELD_MODULUS));

    re.poly_barrett_reduce()
}
