use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{PolynomialRingElement, VECTORS_IN_RING_ELEMENT, ZETAS_TIMES_MONTGOMERY_R},
    vector::{montgomery_multiply_fe, Operations},
};

#[inline(always)]
pub(crate) fn ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        *zeta_i += 1;
        re.coefficients[round] = Vector::ntt_layer_1_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 2],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 3],
        );
        *zeta_i += 3;
    }
    ()
}

#[inline(always)]
pub(crate) fn ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        *zeta_i += 1;
        re.coefficients[round] = Vector::ntt_layer_2_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
        );
        *zeta_i += 1;
    }
    ()
}

#[inline(always)]
pub(crate) fn ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        *zeta_i += 1;
        re.coefficients[round] =
            Vector::ntt_layer_3_step(re.coefficients[round], ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);
    }
    ()
}

#[inline(always)]
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
pub(crate) fn ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
    _initial_coefficient_bound: usize,
) {
    debug_assert!(layer >= 4);
    let step = 1 << layer;

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
                ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            );
            re.coefficients[j] = x;
            re.coefficients[j + step_vec] = y;
        }
    }
    ()
}

#[inline(always)]
pub(crate) fn ntt_at_layer_7<Vector: Operations>(re: &mut PolynomialRingElement<Vector>) {
    let step = VECTORS_IN_RING_ELEMENT / 2;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for j in 0..step {
        let t = Vector::multiply_by_constant(re.coefficients[j + step], -1600);
        re.coefficients[j + step] = Vector::sub(re.coefficients[j], &t);
        re.coefficients[j] = Vector::add(re.coefficients[j], &t);
    }
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
