use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{PolynomialRingElement, ZETAS_TIMES_MONTGOMERY_R},
    vector::{montgomery_multiply_fe, Operations, FIELD_ELEMENTS_IN_VECTOR},
};

#[inline(always)]
pub(crate) fn invert_ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
) {
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        *zeta_i -= 1;
        re.coefficients[round] = Vector::inv_ntt_layer_1_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - 2],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - 3],
        );
        *zeta_i -= 3;
    }
    ()
}

#[inline(always)]
pub(crate) fn invert_ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
) {
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        *zeta_i -= 1;
        re.coefficients[round] = Vector::inv_ntt_layer_2_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - 1],
        );
        *zeta_i -= 1;
    }
    ()
}

#[inline(always)]
pub(crate) fn invert_ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
) {
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        *zeta_i -= 1;
        re.coefficients[round] =
            Vector::inv_ntt_layer_3_step(re.coefficients[round], ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);
    }
    ()
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_int_vec_step_reduce<Vector: Operations>(
    mut a: Vector,
    mut b: Vector,
    zeta_r: i16,
) -> (Vector, Vector) {
    let a_minus_b = Vector::sub(b, &a);
    a = Vector::barrett_reduce(Vector::add(a, &b));
    b = montgomery_multiply_fe::<Vector>(a_minus_b, zeta_r);
    (a, b)
}
#[inline(always)]
pub(crate) fn invert_ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
) {
    let step = 1 << layer;

    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..(128 >> layer) {
        *zeta_i -= 1;

        let offset = round * step * 2;
        let offset_vec = offset / FIELD_ELEMENTS_IN_VECTOR;
        let step_vec = step / FIELD_ELEMENTS_IN_VECTOR;

        for j in offset_vec..offset_vec + step_vec {
            let (x, y) = inv_ntt_layer_int_vec_step_reduce(
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
