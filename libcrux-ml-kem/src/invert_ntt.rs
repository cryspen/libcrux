use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{PolynomialRingElement, get_zeta},
    vector::{montgomery_multiply_fe, Operations, FIELD_ELEMENTS_IN_VECTOR},
};

#[inline(always)]
#[cfg_attr(hax, hax_lib::fstar::before("let zetas_b_lemma (i:nat{i >= 0 /\\ i < 128}) : Lemma
   (Spec.Utils.is_i16b 1664 ${ZETAS_TIMES_MONTGOMERY_R}.[ sz i ]) =
   admit()"))]
#[hax_lib::requires(fstar!("v ${*zeta_i} >= 64 && v ${*zeta_i} <= 128"))]
pub(crate) fn invert_ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
) {
    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init - v $round * 4") });
        *zeta_i -= 1;
        hax_lib::fstar!("zetas_b_lemma (v zeta_i);
            zetas_b_lemma (v zeta_i - 1);
            zetas_b_lemma (v zeta_i - 2);
            zetas_b_lemma (v zeta_i - 3)");
        re.coefficients[round] = Vector::inv_ntt_layer_1_step(
            re.coefficients[round],
            get_zeta (*zeta_i),
            get_zeta (*zeta_i - 1),
            get_zeta (*zeta_i - 2),
            get_zeta (*zeta_i - 3),
        );
        *zeta_i -= 3;
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(fstar!("v ${*zeta_i} >= 32 && v ${*zeta_i} <= 128"))]
pub(crate) fn invert_ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
) {
    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init - v $round * 2") });
        *zeta_i -= 1;
        hax_lib::fstar!("zetas_b_lemma (v zeta_i);
            zetas_b_lemma (v zeta_i - 1)");
        re.coefficients[round] = Vector::inv_ntt_layer_2_step(
            re.coefficients[round],
            get_zeta (*zeta_i),
            get_zeta (*zeta_i - 1),
        );
        *zeta_i -= 1;
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(fstar!("v ${*zeta_i} >= 16 && v ${*zeta_i} <= 128"))]
pub(crate) fn invert_ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
) {
    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init - v $round") });
        *zeta_i -= 1;
        hax_lib::fstar!("zetas_b_lemma (v zeta_i)");
        re.coefficients[round] =
            Vector::inv_ntt_layer_3_step(re.coefficients[round], get_zeta (*zeta_i));
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(fstar!("Spec.Utils.is_i16b 3328 $zeta_r /\\
    Spec.Utils.is_i16b_array 28296 (Libcrux_ml_kem.Vector.Traits.f_to_i16_array
        (Libcrux_ml_kem.Vector.Traits.f_add $a $b))"))]
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
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::requires(fstar!("v $layer >= 4 /\\ v $layer <= 7 /\\
    v ${*zeta_i} - v (sz 128 >>! $layer) >= 0 /\\ v ${*zeta_i} <= 128"))]
pub(crate) fn invert_ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
) {
    let step = 1 << layer;

    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..(128 >> layer) {
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init - v $round") });
        hax_lib::fstar!("assert (v $round < 8);
          assert (v $step >= 16 /\\ v $step <= 128);
          assert (v ($round *! $step) >= 0 /\\ v ($round *! $step) <= 112)");
        *zeta_i -= 1;

        let offset = round * step * 2;
        hax_lib::fstar!("assert (v $offset >= 0 /\\ v $offset <= 224)");
        let offset_vec = offset / FIELD_ELEMENTS_IN_VECTOR;
        let step_vec = step / FIELD_ELEMENTS_IN_VECTOR;

        for j in offset_vec..offset_vec + step_vec {
            hax_lib::fstar!("zetas_b_lemma (v zeta_i)");
            hax_lib::fstar!("assume (Spec.Utils.is_i16b_array 28296
                (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (Libcrux_ml_kem.Vector.Traits.f_add re.f_coefficients.[j] re.f_coefficients.[j +! step_vec])))");
            let (x, y) = inv_ntt_layer_int_vec_step_reduce(
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
#[hax_lib::fstar::options("--z3rlimit 200")]
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
