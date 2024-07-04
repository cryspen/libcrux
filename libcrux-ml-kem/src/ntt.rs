use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{PolynomialRingElement, VECTORS_IN_RING_ELEMENT, ZETAS_TIMES_MONTGOMERY_R},
    vector::{montgomery_multiply_fe, Operations},
};

use hax_lib::*;
use hax_lib::int::*;

#[cfg_attr(hax, requires(
    *zeta_i < 64
))]
#[inline(always)]
pub(crate) fn ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    for round in 0..16 {
        hax_lib::assert!(*zeta_i + (round * 4) + 1 < 128);
        hax_lib::assert!(*zeta_i + (round * 4) + 2 < 128);
        hax_lib::assert!(*zeta_i + (round * 4) + 3 < 128);
        hax_lib::assert!(*zeta_i + (round * 4) + 4 < 128);
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_ntt_layer_1_step_pre #v_Vector
                    (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i +!
                          (round *! sz 4 <: usize)
                          <:
                          usize) +!
                        sz 1
                        <:
                        usize ]
                      <:
                      i16)
                    (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i +!
                          (round *! sz 4 <: usize)
                          <:
                          usize) +!
                        sz 2
                        <:
                        usize ]
                      <:
                      i16)
                    (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i +!
                          (round *! sz 4 <: usize)
                          <:
                          usize) +!
                        sz 3
                        <:
                        usize ]
                      <:
                      i16)
                    (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i +!
                          (round *! sz 4 <: usize)
                          <:
                          usize) +!
                        sz 4
                        <:
                        usize ]
                      <:
                      i16))");
        re.coefficients[round] = Vector::ntt_layer_1_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + (round * 4) + 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + (round * 4) + 2],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + (round * 4) + 3],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + (round * 4) + 4],
        );
    }
    *zeta_i += 64;
}

#[cfg_attr(hax, requires(
    *zeta_i < 96
))]
#[inline(always)]
pub(crate) fn ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    for round in 0..16 {
        hax_lib::assert!(*zeta_i + (round * 2) + 1 < 128);
        hax_lib::assert!(*zeta_i + (round * 2) + 2 < 128);
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_ntt_layer_2_step_pre #v_Vector
                  (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                  (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i +!
                        (round *! sz 2 <: usize)
                        <:
                        usize) +!
                      sz 1
                      <:
                      usize ]
                    <:
                    i16)
                  (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i +!
                        (round *! sz 2 <: usize)
                        <:
                        usize) +!
                      sz 2
                      <:
                      usize ]
                    <:
                    i16))");
        re.coefficients[round] = Vector::ntt_layer_2_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + (round * 2) + 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + (round * 2) + 2],
        );
    }
    *zeta_i += 32;
}

#[cfg_attr(hax, requires(
    *zeta_i < 112
))]
#[inline(always)]
pub(crate) fn ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    for round in 0..16 {
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_ntt_layer_3_step_pre #v_Vector
                  (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                  (Libcrux_ml_kem.Polynomial.v_ZETAS_TIMES_MONTGOMERY_R.[ (zeta_i +! round <: usize) +!
                      sz 1
                      <:
                      usize ]
                    <:
                    i16))");
        re.coefficients[round] =
            Vector::ntt_layer_3_step(re.coefficients[round], ZETAS_TIMES_MONTGOMERY_R[*zeta_i + round + 1]);
    }
    *zeta_i += 16;
}

#[inline(always)]
fn ntt_layer_int_vec_step<Vector: Operations>(
    mut a: Vector,
    mut b: Vector,
    zeta_r: i16,
) -> (Vector, Vector) {
    let t = montgomery_multiply_fe::<Vector>(b, zeta_r);
    fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_sub_pre #v_Vector a t)");
    b = Vector::sub(a, &t);
    fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_add_pre #v_Vector a t)");
    a = Vector::add(a, &t);
    (a, b)
}
#[cfg_attr(hax, requires(
    layer.lift() < usize::BITS.lift()
    //&& *zeta_i + (128 >> layer) < usize::MAX (Why it works without this!)
))]
#[inline(always)]
pub(crate) fn ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
    _initial_coefficient_bound: usize,
) {
    std::debug_assert!(layer >= 4);
    let step = 1 << layer;

    for round in 0..(128 >> layer) {
        let offset = round * step * 2;
        let offset_vec = offset / 16; //FIELD_ELEMENTS_IN_VECTOR;
        let step_vec = step / 16; //FIELD_ELEMENTS_IN_VECTOR;

        for j in offset_vec..offset_vec + step_vec {
            let (x, y) = ntt_layer_int_vec_step(
                re.coefficients[j],
                re.coefficients[j + step_vec],
                ZETAS_TIMES_MONTGOMERY_R[*zeta_i + round + 1],
            );
            re.coefficients[j] = x;
            re.coefficients[j + step_vec] = y;
        }
    }
    *zeta_i += 128 >> layer;
}

#[inline(always)]
pub(crate) fn ntt_at_layer_7<Vector: Operations>(re: &mut PolynomialRingElement<Vector>) {
    let step = VECTORS_IN_RING_ELEMENT / 2;
    for j in 0..step {
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_multiply_by_constant_pre #v_Vector
            (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ j +! step <: usize ] <: v_Vector)
            (-1600s))");
        let t = Vector::multiply_by_constant(re.coefficients[j + step], -1600);
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_sub_pre #v_Vector
            (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ j ] <: v_Vector)
            t)");
        re.coefficients[j + step] = Vector::sub(re.coefficients[j], &t);
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_add_pre #v_Vector
            (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ j ] <: v_Vector)
            t)");
        re.coefficients[j] = Vector::add(re.coefficients[j], &t);
    };
    ()
}

#[inline(always)]
pub(crate) fn ntt_binomially_sampled_ring_element<Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
) {
    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.
    ntt_at_layer_7(re);

    let mut zeta_i = 1;
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, 3);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, 3);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, 3);
    ntt_at_layer_3(&mut zeta_i, re, 3, 3);
    ntt_at_layer_2(&mut zeta_i, re, 2, 3);
    ntt_at_layer_1(&mut zeta_i, re, 1, 3);

    re.poly_barrett_reduce()
}

#[inline(always)]
pub(crate) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    ntt_at_layer_4_plus(&mut zeta_i, re, 7, 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, 3328);
    ntt_at_layer_3(&mut zeta_i, re, 3, 3328);
    ntt_at_layer_2(&mut zeta_i, re, 2, 3328);
    ntt_at_layer_1(&mut zeta_i, re, 1, 3328);

    re.poly_barrett_reduce()
}
