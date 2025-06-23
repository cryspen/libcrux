use crate::{
    constants::{Gamma2, COEFFICIENTS_IN_RING_ELEMENT},
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"v $bound > 0 /\ 
        (forall i. forall j. Spec.Utils.is_i32b_array_opaque 
            (v ${crate::simd::traits::specs::FIELD_MAX}) 
            (i1._super_4202118595671791609.f_repr (Seq.index (Seq.index vector i).f_simd_units j)))"#))]
pub(crate) fn vector_infinity_norm_exceeds<SIMDUnit: Operations>(
    vector: &[PolynomialRingElement<SIMDUnit>],
    bound: i32,
) -> bool {
    let mut result = false;
    for i in 0..vector.len() {
        result = result || vector[i].infinity_norm_exceeds(bound);
    }
    result
}

#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"v $SHIFT_BY == 13 /\ 
        (forall i. forall j.
            v (Seq.index (i1._super_4202118595671791609.f_repr (Seq.index re.f_simd_units i)) j) >= 0 /\
            v (Seq.index (i1._super_4202118595671791609.f_repr (Seq.index re.f_simd_units i)) j) <= 261631)"#))]
pub(crate) fn shift_left_then_reduce<SIMDUnit: Operations, const SHIFT_BY: i32>(
    re: &mut PolynomialRingElement<SIMDUnit>,
) {
    #[cfg(hax)]
    let old_re = re.clone();

    for i in 0..re.simd_units.len() {
        hax_lib::loop_invariant!(|i: usize| fstar!(
            r#"
            forall j. j >= v i ==> Seq.index re.f_simd_units j == Seq.index old_re.f_simd_units j"#
        ));

        SIMDUnit::shift_left_then_reduce::<SHIFT_BY>(&mut re.simd_units[i]);
    }
}

#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"${t.len()} == ${t1.len()} /\
    (forall i. forall j. 
        Spec.Utils.is_i32b_array_opaque 
        (v ${crate::simd::traits::specs::FIELD_MAX}) 
        (i1._super_4202118595671791609.f_repr (Seq.index (Seq.index t i).f_simd_units j)))"#))]
pub(crate) fn power2round_vector<SIMDUnit: Operations>(
    t: &mut [PolynomialRingElement<SIMDUnit>],
    t1: &mut [PolynomialRingElement<SIMDUnit>],
) {
    #[cfg(hax)]
    let (old_t, old_t1) = { (t.to_vec(), t1.to_vec()) };

    for i in 0..t.len() {
        hax_lib::loop_invariant!(|i: usize| fstar!(
            r#"
            ${t.len()} == ${old_t.len()} /\
            ${t1.len()} == ${old_t1.len()} /\
            (forall j. j >= v i ==> 
                (Seq.index t j == Seq.index old_t j /\
                 Seq.index t1 j == Seq.index old_t1 j))
            "#
        ));

        for j in 0..t[i].simd_units.len() {
            hax_lib::loop_invariant!(|j: usize| fstar!(
                r#"
                ${t.len()} == ${old_t.len()} /\
                ${t1.len()} == ${old_t1.len()} /\
                (forall j. j > v i ==> 
                    (Seq.index t j == Seq.index old_t j /\
                     Seq.index t1 j == Seq.index old_t1 j)) /\
                (forall k. k >= v j ==> 
                    (Seq.index (Seq.index t (v i)).f_simd_units k ==
                     Seq.index (Seq.index old_t (v i)).f_simd_units k /\
                     Seq.index (Seq.index t1 (v i)).f_simd_units k ==
                     Seq.index (Seq.index old_t1 (v i)).f_simd_units k))
                "#
            ));

            SIMDUnit::power2round(&mut t[i].simd_units[j], &mut t1[i].simd_units[j]);
        }
    }
}

#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/ 
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
         ${t.len()} == dimension /\ 
         ${low.len()} == dimension /\
         ${high.len()} == dimension /\
         (forall i. forall j. 
            Spec.Utils.is_i32b_array_opaque 
            (v ${crate::simd::traits::specs::FIELD_MAX}) 
            (i1._super_4202118595671791609.f_repr (Seq.index (Seq.index t i).f_simd_units j)))"#))]
pub(crate) fn decompose_vector<SIMDUnit: Operations>(
    dimension: usize,
    gamma2: Gamma2,
    t: &[PolynomialRingElement<SIMDUnit>],
    low: &mut [PolynomialRingElement<SIMDUnit>],
    high: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..dimension {
        hax_lib::loop_invariant!(|i: usize| low.len() == dimension && high.len() == dimension);

        for j in 0..low[0].simd_units.len() {
            hax_lib::loop_invariant!(|i: usize| low.len() == dimension && high.len() == dimension);

            SIMDUnit::decompose(
                gamma2,
                &t[i].simd_units[j],
                &mut low[i].simd_units[j],
                &mut high[i].simd_units[j],
            );
        }
    }
}

#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/ 
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
         ${low.len()} == ${high.len()} /\ 
         ${low.len()} == ${hint.len()} /\
         v (${low.len()}) <= 8"#))]
pub(crate) fn make_hint<SIMDUnit: Operations>(
    low: &[PolynomialRingElement<SIMDUnit>],
    high: &[PolynomialRingElement<SIMDUnit>],
    gamma2: i32,
    hint: &mut [[i32; COEFFICIENTS_IN_RING_ELEMENT]],
) -> usize {
    let mut true_hints = 0;
    let mut hint_simd = PolynomialRingElement::<SIMDUnit>::zero();

    for i in 0..low.len() {
        hax_lib::loop_invariant!(|i: usize| true_hints <= 256 * i && hint.len() == low.len());

        for j in 0..hint_simd.simd_units.len() {
            hax_lib::loop_invariant!(|j: usize| true_hints <= 256 * i + 8 * j);

            let one_hints_count = SIMDUnit::compute_hint(
                &low[i].simd_units[j],
                &high[i].simd_units[j],
                gamma2,
                &mut hint_simd.simd_units[j],
            );

            true_hints += one_hints_count;
        }

        hint[i] = hint_simd.to_i32_array();
    }

    true_hints
}

#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/ 
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
         ${hint.len()} == ${re_vector.len()} /\ 
         v (${hint.len()}) <= 8 /\
         (forall i. forall j.
            (v (Seq.index (Seq.index ${hint} i) j) == 0 \/ 
             v (Seq.index (Seq.index ${hint} i) j) == 1)) /\
         (forall i. forall j. 
            Spec.Utils.is_i32b_array_opaque 
            (v ${crate::simd::traits::specs::FIELD_MAX}) 
            (i1._super_4202118595671791609.f_repr (Seq.index (Seq.index re_vector i).f_simd_units j)))"#))]
pub(crate) fn use_hint<SIMDUnit: Operations>(
    gamma2: Gamma2,
    hint: &[[i32; COEFFICIENTS_IN_RING_ELEMENT]],
    re_vector: &mut [PolynomialRingElement<SIMDUnit>],
) {
    #[cfg(hax)]
    let old_re_vector = re_vector.to_vec();

    for i in 0..re_vector.len() {
        hax_lib::loop_invariant!(|i: usize| fstar!(
            r#"
            ${re_vector.len()} == ${hint.len()} /\
            (forall j. j >= v i ==> 
                (Seq.index re_vector j == Seq.index old_re_vector j))
            "#
        ));

        let mut tmp = PolynomialRingElement::zero();
        PolynomialRingElement::<SIMDUnit>::from_i32_array(&hint[i], &mut tmp);

        for j in 0..re_vector[0].simd_units.len() {
            hax_lib::loop_invariant!(|j: usize| fstar!(
                r#"
                ${re_vector.len()} == ${hint.len()} /\
                (forall j. j > v i ==> 
                    (Seq.index re_vector j == Seq.index old_re_vector j)) /\
                (forall k. k >= v j ==> 
                    (Seq.index (Seq.index re_vector (v i)).f_simd_units k ==
                     Seq.index (Seq.index old_re_vector (v i)).f_simd_units k))
                "#
            ));

            SIMDUnit::use_hint(gamma2, &re_vector[i].simd_units[j], &mut tmp.simd_units[j]);
        }
        re_vector[i] = tmp;
    }
}
