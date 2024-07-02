use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{PolynomialRingElement, ZETAS_TIMES_MONTGOMERY_R},
    vector::{montgomery_multiply_fe, Operations, FIELD_ELEMENTS_IN_VECTOR},
};

use hax_lib::*;
use hax_lib::int::*;

#[cfg_attr(hax, requires(
    *zeta_i >= 64 && *zeta_i <= 128
))]
#[inline(always)]
pub(crate) fn invert_ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
) {
    for round in 0..16 {
        hax_lib::assert!(*zeta_i - (round * 4) - 1 >= 0);
        hax_lib::assert!(*zeta_i - (round * 4) - 2 >= 0);
        hax_lib::assert!(*zeta_i - (round * 4) - 3 >= 0);
        hax_lib::assert!(*zeta_i - (round * 4) - 4 >= 0);
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_inv_ntt_layer_1_step_pre #v_Vector
                  (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                  (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i -!
                        (round *! sz 4 <: usize)
                        <:
                        usize) -!
                      sz 1
                      <:
                      usize ]
                    <:
                    i16)
                  (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i -!
                        (round *! sz 4 <: usize)
                        <:
                        usize) -!
                      sz 2
                      <:
                      usize ]
                    <:
                    i16)
                  (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i -!
                        (round *! sz 4 <: usize)
                        <:
                        usize) -!
                      sz 3
                      <:
                      usize ]
                    <:
                    i16)
                  (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i -!
                        (round *! sz 4 <: usize)
                        <:
                        usize) -!
                      sz 4
                      <:
                      usize ]
                    <:
                    i16))");
        re.coefficients[round] = Vector::inv_ntt_layer_1_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - (round * 4) - 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - (round * 4) - 2],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - (round * 4) - 3],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - (round * 4) - 4],
        );
    }
    *zeta_i -= 64;
}

#[cfg_attr(hax, requires(
    *zeta_i >= 32 && *zeta_i <= 128
))]
#[inline(always)]
pub(crate) fn invert_ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
) {
    for round in 0..16 {
        hax_lib::assert!(*zeta_i - (round * 2) - 1 >= 0);
        hax_lib::assert!(*zeta_i - (round * 2) - 2 >= 0);
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_inv_ntt_layer_2_step_pre #v_Vector
                    (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i -!
                          (round *! sz 2 <: usize)
                          <:
                          usize) -!
                        sz 1
                        <:
                        usize ]
                      <:
                      i16)
                    (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i -!
                          (round *! sz 2 <: usize)
                          <:
                          usize) -!
                        sz 2
                        <:
                        usize ]
                      <:
                      i16))");
        re.coefficients[round] = Vector::inv_ntt_layer_2_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - (round * 2) - 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - (round * 2) - 2],
        );
    }
    *zeta_i -= 32;
}

#[cfg_attr(hax, requires(
    *zeta_i >= 16 && *zeta_i <= 128
))]
#[inline(always)]
pub(crate) fn invert_ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
) {
    for round in 0..16 {
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_inv_ntt_layer_3_step_pre #v_Vector
                    (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i -! round
                          <:
                          usize) -!
                        sz 1
                        <:
                        usize ]
                      <:
                      i16))");
        re.coefficients[round] =
            Vector::inv_ntt_layer_3_step(re.coefficients[round], ZETAS_TIMES_MONTGOMERY_R[*zeta_i - round - 1]);
    }
    *zeta_i -= 16;
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_int_vec_step_reduce<Vector: Operations>(
    mut a: Vector,
    mut b: Vector,
    zeta_r: i16,
) -> (Vector, Vector) {
    fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_sub_pre #v_Vector b a)");
    let a_minus_b = Vector::sub(b, &a);
    fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_add_pre #v_Vector a b)");
    fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce_pre #v_Vector
      (Libcrux_ml_kem.Vector.Traits.f_add #v_Vector a b <: v_Vector))");
    a = Vector::barrett_reduce(Vector::add(a, &b));
    b = montgomery_multiply_fe::<Vector>(a_minus_b, zeta_r);
    (a, b)
}
#[cfg_attr(hax, requires(
    layer.lift() < usize::BITS.lift() &&
    *zeta_i - (128 >> layer) >= 0
))]
#[inline(always)]
pub(crate) fn invert_ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
) {
    let step = 1 << layer;

    for round in 0..(128 >> layer) {
        let offset = round * step * 2;
        let offset_vec = offset / FIELD_ELEMENTS_IN_VECTOR;
        let step_vec = step / FIELD_ELEMENTS_IN_VECTOR;

        for j in offset_vec..offset_vec + step_vec {
            let (x, y) = inv_ntt_layer_int_vec_step_reduce(
                re.coefficients[j],
                re.coefficients[j + step_vec],
                ZETAS_TIMES_MONTGOMERY_R[*zeta_i - round - 1],
            );
            re.coefficients[j] = x;
            re.coefficients[j + step_vec] = y;
        }
    }
    *zeta_i -= 128 >> layer;
}

#[inline(always)]
pub(crate) fn invert_ntt_montgomery<const K: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
) {
    // We only ever call this function after matrix/vector multiplication
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() < (K as i16) * FIELD_MODULUS));

    let mut zeta_i = super::constants::COEFFICIENTS_IN_RING_ELEMENT / 2;

    invert_ntt_at_layer_1(&mut zeta_i, re, 1);
    invert_ntt_at_layer_2(&mut zeta_i, re, 2);
    invert_ntt_at_layer_3(&mut zeta_i, re, 3);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 4);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 5);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 6);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 7);

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
