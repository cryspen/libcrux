use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{zeta, PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    vector::{traits::montgomery_multiply_fe, Operations, FIELD_ELEMENTS_IN_VECTOR},
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
               (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ sz i ]))"
)]
#[hax_lib::fstar::before(
    interface,
    "[@@ \"opaque_to_smt\"]
   let invert_ntt_re_range_1 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (4 * 3328)
            (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ sz i ]))"
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
    #[cfg(hax)]
    let _zeta_i_init = *zeta_i;

    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            fstar!(
                r#"v zeta_i == v $_zeta_i_init - v $round * 4 /\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque (4 * 3328)
              (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ sz i ])))) /\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque 3328
              (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ sz i ])))"#
            )
        });
        *zeta_i -= 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (4*3328) 
                        (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ round ])))"#
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
                        (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ round ])))"#
        );
        hax_lib::fstar!(
            "assert (Spec.Utils.is_i16b_array_opaque 3328
            (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ $round ])))"
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
    #[cfg(hax)]
    let _zeta_i_init = *zeta_i;

    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            fstar!(
                r#"v zeta_i == v $_zeta_i_init - v $round * 2 /\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque 3328
              (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ sz i ])))) /\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque 3328
              (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ sz i ])))"#
            )
        });
        *zeta_i -= 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328 
                        (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ round ])))"#
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
                        (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ round ])))"#
        );
        hax_lib::fstar!(
            "assert (Spec.Utils.is_i16b_array_opaque 3328
            (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ $round ])))"
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
    #[cfg(hax)]
    let _zeta_i_init = *zeta_i;

    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| {
            fstar!(
                r#"v zeta_i == v $_zeta_i_init - v $round /\
          (v round < 16 ==> (forall (i:nat). (i >= v round /\ i < 16) ==>
            Spec.Utils.is_i16b_array_opaque 3328
              (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ sz i ])))) /\
          (forall (i:nat). i < v $round ==> Spec.Utils.is_i16b_array_opaque 3328
              (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ sz i ])))"#
            )
        });
        *zeta_i -= 1;
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328 
                        (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ round ])))"#
        );
        Vector::inv_ntt_layer_3_step(&mut re.coefficients[round], zeta(*zeta_i));
        hax_lib::fstar!(
            "reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
            (Spec.Utils.is_i16b_array_opaque 3328 
            (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ round ])))"
        );
        hax_lib::fstar!(
            "assert (Spec.Utils.is_i16b_array_opaque 3328
            (Libcrux_ml_kem.Vector.Traits.f_repr (re.f_coefficients.[ $round ])))"
        );
    }
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 $zeta_r /\
    v $a < 16 /\ v $b < 16 /\
   (let vec_a = Seq.index $coefficients (v $a) in
    let vec_b = Seq.index $coefficients (v $b) in
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (i0._super_6081346371236564305.f_repr vec_b) i) -
        v (Seq.index (i0._super_6081346371236564305.f_repr vec_a) i))) /\
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (i0._super_6081346371236564305.f_repr vec_b) i) +
        v (Seq.index (i0._super_6081346371236564305.f_repr vec_a) i))) /\
    Spec.Utils.is_i16b_array 28296 (i0._super_6081346371236564305.f_repr
        (Libcrux_ml_kem.Vector.Traits.f_add vec_a vec_b)))"#))]
pub(crate) fn inv_ntt_layer_int_vec_step_reduce<Vector: Operations>(
    coefficients: &mut [Vector; VECTORS_IN_RING_ELEMENT],
    a: usize,
    b: usize,
    scratch: &mut PolynomialRingElement<Vector>,
    zeta_r: i16,
) {
    // XXX: Making the clones explicit, since we would like to drop `Vector: Copy` in the future.
    scratch.coefficients[0] = coefficients[a].clone();
    scratch.coefficients[1] = coefficients[b].clone();

    Vector::add(&mut coefficients[a], &scratch.coefficients[1]);
    Vector::sub(&mut coefficients[b], &scratch.coefficients[0]);
    Vector::barrett_reduce(&mut coefficients[a]);
    montgomery_multiply_fe::<Vector>(&mut coefficients[b], zeta_r);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"v $layer >= 4 /\ v $layer <= 7"#))]
pub(crate) fn invert_ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
    scratch: &mut PolynomialRingElement<Vector>,
) {
    let step = 1 << layer;
    let step_vec = step / FIELD_ELEMENTS_IN_VECTOR;

    for round in 0..(128 >> layer) {
        *zeta_i -= 1;

        let a_offset = round * 2 * step_vec;
        let b_offset = a_offset + step_vec;

        for j in 0..step_vec {
            inv_ntt_layer_int_vec_step_reduce(
                &mut re.coefficients,
                a_offset + j,
                b_offset + j,
                scratch,
                zeta(*zeta_i),
            );
        }
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"invert_ntt_re_range_1 $re"#))]
pub(crate) fn invert_ntt_montgomery<const K: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut PolynomialRingElement<Vector>,
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

    re.poly_barrett_reduce();
}
