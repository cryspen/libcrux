use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{PolynomialRingElement, VECTORS_IN_RING_ELEMENT, get_zeta},
    vector::{montgomery_multiply_fe, Operations},
};

#[inline(always)]
#[cfg_attr(hax, hax_lib::fstar::before("let zetas_b_lemma (i:nat{i >= 0 /\\ i < 128}) : Lemma
   (Spec.Utils.is_i16b 1664 (${get_zeta} (sz i))) =
   admit()"))]
#[hax_lib::requires(fstar!("v ${*zeta_i} < 64"))]
pub(crate) fn ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init + v $round * 4") });
        *zeta_i += 1;
        hax_lib::fstar!("zetas_b_lemma (v zeta_i);
            zetas_b_lemma (v zeta_i + 1);
            zetas_b_lemma (v zeta_i + 2);
            zetas_b_lemma (v zeta_i + 3)");
        re.coefficients[round] = Vector::ntt_layer_1_step(
            re.coefficients[round],
            get_zeta (*zeta_i),
            get_zeta (*zeta_i + 1),
            get_zeta (*zeta_i + 2),
            get_zeta (*zeta_i + 3),
        );
        *zeta_i += 3;
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(fstar!("v ${*zeta_i} < 96"))]
pub(crate) fn ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init + v $round * 2") });
        *zeta_i += 1;
        hax_lib::fstar!("zetas_b_lemma (v zeta_i);
            zetas_b_lemma (v zeta_i + 1)");
        re.coefficients[round] = Vector::ntt_layer_2_step(
            re.coefficients[round],
            get_zeta (*zeta_i),
            get_zeta (*zeta_i + 1),
        );
        *zeta_i += 1;
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(fstar!("v ${*zeta_i} < 112"))]
pub(crate) fn ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) {
    let _zeta_i_init = *zeta_i;
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for round in 0..16 {
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init + v $round") });
        *zeta_i += 1;
        hax_lib::fstar!("zetas_b_lemma (v zeta_i)");
        re.coefficients[round] =
            Vector::ntt_layer_3_step(re.coefficients[round], get_zeta (*zeta_i));
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(fstar!("Spec.Utils.is_i16b 1664 $zeta_r /\\
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array $a) i) -
        v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array
            (Libcrux_ml_kem.Vector.Traits.montgomery_multiply_fe $b $zeta_r)) i))) /\\
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array $a) i) +
        v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array
            (Libcrux_ml_kem.Vector.Traits.montgomery_multiply_fe $b $zeta_r)) i)))"))]
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
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::requires(fstar!("v $layer >= 4 /\\ v $layer <= 7 /\\
    v ${*zeta_i} + v (sz 128 >>! $layer) < 128"))]
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
        hax_lib::loop_invariant!(|round: usize| { fstar!("v zeta_i == v $_zeta_i_init + v $round") });
        hax_lib::fstar!("assert (v $round < 8);
          assert (v $step >= 16 /\\ v $step <= 128);
          assert (v ($round *! $step) >= 0 /\\ v ($round *! $step) <= 112)");
        *zeta_i += 1;

        let offset = round * step * 2;
        hax_lib::fstar!("assert (v $offset >= 0 /\\ v $offset <= 224)");
        let offset_vec = offset / 16; //FIELD_ELEMENTS_IN_VECTOR;
        let step_vec = step / 16; //FIELD_ELEMENTS_IN_VECTOR;

        for j in offset_vec..offset_vec + step_vec {
            hax_lib::fstar!("zetas_b_lemma (v zeta_i)");
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
