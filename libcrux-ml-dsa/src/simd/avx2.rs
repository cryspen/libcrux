use crate::{
    constants::{Eta, Gamma2},
    simd::traits::*,
};

mod arithmetic;
mod encoding;
mod invntt;
mod ntt;
mod rejection_sample;
mod vector_type;

use arithmetic::shift_left_then_reduce;
pub(crate) use vector_type::{AVX2RingElement, Vec256 as AVX2SIMDUnit};

#[cfg(hax)]
use crate::simd::traits::specs;

#[cfg(hax)]
impl Repr for AVX2SIMDUnit {
    fn repr(&self) -> [i32; COEFFICIENTS_IN_SIMD_UNIT] {
        let mut result = [0i32; COEFFICIENTS_IN_SIMD_UNIT];
        vector_type::to_coefficient_array(self, &mut result);
        result
    }
}

#[cfg(not(hax))]
impl Repr for AVX2SIMDUnit {}

// ---------------------------------------------------------------------------
// Track B (Step 10): one-line-wrapper refactor for non-trivial impl methods.
// See `src/simd/portable.rs` for the Portable counterparts and rationale.
// ---------------------------------------------------------------------------

#[inline(always)]
#[hax_lib::requires(fstar!(r#"v $bound > 0 /\
    Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
#[hax_lib::ensures(|result| fstar!(r#"
    Libcrux_ml_dsa.Simd.Traits.Specs.infinity_norm_exceeds_post
        (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) $bound $result"#))]
pub(crate) fn infinity_norm_exceeds_with_proof(simd_unit: &AVX2SIMDUnit, bound: i32) -> bool {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Spec.Utils.is_i32b_array_opaque)
            (Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
                (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}));
        let _r = Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit} in
        assert (forall (i: u64). v i < 8 ==>
            Spec.Utils.is_i32b 8380416
                (Spec.Intrinsics.to_i32x8
                    ${simd_unit}.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value i))"#
    );
    let result = arithmetic::infinity_norm_exceeds(&simd_unit.value, bound);
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_dsa.Simd.Traits.Specs.infinity_norm_exceeds_post)
            (Libcrux_ml_dsa.Simd.Traits.Specs.infinity_norm_exceeds_post
                (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) $bound $result)"#
    );
    result
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"v $SHIFT_BY == 13 /\
    (forall i. i < 8 ==> v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i) >= 0 /\
        v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i) <= 261631)"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
      Libcrux_ml_dsa.Simd.Traits.Specs.shift_left_then_reduce_lane_post
        (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i)
        (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}_future) i))"#))]
pub(crate) fn shift_left_then_reduce_with_proof<const SHIFT_BY: i32>(
    simd_unit: &mut AVX2SIMDUnit,
) {
    #[cfg(hax)]
    let _orig = *simd_unit;
    shift_left_then_reduce::<SHIFT_BY>(&mut simd_unit.value);
    hax_lib::fstar!(
        r#"let pf (k: nat{k < 8}) : Lemma
            (ensures Libcrux_ml_dsa.Simd.Traits.Specs.shift_left_then_reduce_lane_post
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig}) k)
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) k)) =
            Hacspec_ml_dsa.Commute.Chunk.lemma_shift_left_then_reduce_lane_commute
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig}) k)
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) k)
        in
        Classical.forall_intro pf"#
    );
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
    Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0})"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.is_i32b_array_opaque (pow2 12) (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}_future) /\
    Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
      v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}_future) i) >= 0 /\
      v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}_future) i) < pow2 10) /\
    Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
      Libcrux_ml_dsa.Simd.Traits.Specs.power2round_lane_post
        (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}) i)
        (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}_future) i)
        (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}_future) i))"#))]
pub(crate) fn power2round_with_proof(t0: &mut AVX2SIMDUnit, t1: &mut AVX2SIMDUnit) {
    #[cfg(hax)]
    let _orig_t0 = *t0;
    hax_lib::fstar!(
        r#"reveal_opaque (`%Spec.Utils.is_i32b_array_opaque)
            (Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
                (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}));
        let _r = Libcrux_ml_dsa.Simd.Traits.f_repr ${t0} in
        assert (forall (i: u64). v i < 8 ==>
            Spec.Utils.is_i32b 8380416
                (Spec.Intrinsics.to_i32x8
                    ${t0}.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value i))"#
    );
    arithmetic::power2round(&mut t0.value, &mut t1.value);
    hax_lib::fstar!(
        r#"
        let pf (k: nat{k < 8}) : Lemma
            (ensures Libcrux_ml_dsa.Simd.Traits.Specs.power2round_lane_post
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig_t0}) k)
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}) k)
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}) k)) =
            Hacspec_ml_dsa.Commute.Chunk.lemma_power2round_lane_commute
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig_t0}) k)
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}) k)
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}) k)
        in
        Classical.forall_intro pf;
        reveal_opaque (`%Spec.Utils.is_i32b_array_opaque)
            (Spec.Utils.is_i32b_array_opaque (pow2 12)
                (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}));
        let pf_t1 (k: nat{k < 8}) : Lemma
            (ensures
                v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}) k) >= 0 /\
                v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}) k) < pow2 10) =
            Hacspec_ml_dsa.Commute.Chunk.lemma_power2round_t1_bound
                (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig_t0}) k)
        in
        Classical.forall_intro pf_t1"#
    );
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
    (forall (i:nat). i < 32 ==>
        Spec.Utils.is_i32b_array_opaque 2143289343
            (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} i)))"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    (forall (j:nat). j < 32 ==>
      Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
        (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units}_future j)) /\
      Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
        Libcrux_ml_dsa.Simd.Traits.Specs.reduce_lane_post
          (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} j)) i)
          (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units}_future j)) i)))"#))]
pub(crate) fn reduce_with_proof(simd_units: &mut [AVX2SIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[cfg(hax)]
    let _orig = simd_units.clone();

    for i in 0..simd_units.len() {
        hax_lib::loop_invariant!(|i: usize| fstar!(r#"
            v $i <= 32 /\
            (forall (j:nat{j < 32}). j < v $i ==>
                (forall (k:nat{k < 8}).
                    Spec.Intrinsics.to_i32x8
                        (Seq.index ${simd_units} j).Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
                        (mk_u64 k) ==
                    Spec.MLDSA.Math.barrett_red
                        (Spec.Intrinsics.to_i32x8
                            (Seq.index ${_orig} j).Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
                            (mk_u64 k)))) /\
            (forall (j:nat{j < 32}). j >= v $i ==>
                Seq.index ${simd_units} j == Seq.index ${_orig} j)"#));

        arithmetic::reduce(&mut simd_units[i].value);
    }

    hax_lib::fstar!(r#"
        let pf (j: nat{j < 32}) : Lemma
            (ensures
                Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
                    (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} j)) /\
                Spec.Utils.forall8 (fun (k: nat{k < 8}) ->
                    Libcrux_ml_dsa.Simd.Traits.Specs.reduce_lane_post
                        (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${_orig} j)) k)
                        (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} j)) k))) =
            reveal_opaque (`%Spec.Utils.is_i32b_array_opaque)
                (Spec.Utils.is_i32b_array_opaque 2143289343
                    (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${_orig} j)));
            let pfk (k: nat{k < 8}) : Lemma
                (ensures Libcrux_ml_dsa.Simd.Traits.Specs.reduce_lane_post
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${_orig} j)) k)
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} j)) k)) =
                Hacspec_ml_dsa.Commute.Chunk.lemma_barrett_red_bound_and_mod_q
                    (Spec.Intrinsics.to_i32x8
                        (Seq.index ${_orig} j).Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
                        (mk_u64 k));
                Hacspec_ml_dsa.Commute.Chunk.lemma_reduce_lane_commute
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${_orig} j)) k)
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} j)) k)
            in
            Classical.forall_intro pfk;
            let pfk_bound (k: nat{k < 8}) : Lemma
                (ensures Spec.Utils.is_i32b 8380416
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} j)) k)) =
                Hacspec_ml_dsa.Commute.Chunk.lemma_barrett_red_bound_and_mod_q
                    (Spec.Intrinsics.to_i32x8
                        (Seq.index ${_orig} j).Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
                        (mk_u64 k))
            in
            Classical.forall_intro pfk_bound;
            reveal_opaque (`%Spec.Utils.is_i32b_array_opaque)
                (Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
                    (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} j)))
        in
        Classical.forall_intro pf
    "#);
}

/// Implementing the [`Operations`] for AVX2.
#[hax_lib::attributes]
impl Operations for AVX2SIMDUnit {
    #[inline(always)]
    #[ensures(|result| result.repr() == [0i32; COEFFICIENTS_IN_SIMD_UNIT])]
    fn zero() -> Self {
        hax_lib::fstar!("admit ()");
        vector_type::zero()
    }

    #[inline(always)]
    #[requires(coefficient_array.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[ensures(|_| future(out).repr() == coefficient_array)]
    fn from_coefficient_array(coefficient_array: &[i32], out: &mut Self) {
        hax_lib::fstar!("admit ()");
        vector_type::from_coefficient_array(coefficient_array, out)
    }

    #[inline(always)]
    #[requires(out.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[ensures(|_| future(out) == value.repr())]
    fn to_coefficient_array(value: &Self, out: &mut [i32]) {
        hax_lib::fstar!("admit ()");
        vector_type::to_coefficient_array(value, out)
    }

    #[inline(always)]
    #[requires(specs::add_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|_| specs::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn add(lhs: &mut Self, rhs: &Self) {
        #[cfg(hax)]
        let _orig = *lhs;
        arithmetic::add(&mut lhs.value, &rhs.value);
        hax_lib::fstar!(r#"
            reveal_opaque (`%Libcrux_ml_dsa.Simd.Traits.Specs.add_pre)
                (Libcrux_ml_dsa.Simd.Traits.Specs.add_pre
                    (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig})
                    (Libcrux_ml_dsa.Simd.Traits.f_repr ${rhs}));
            reveal_opaque (`%Libcrux_ml_dsa.Simd.Traits.Specs.add_post)
                (Libcrux_ml_dsa.Simd.Traits.Specs.add_post
                    (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig})
                    (Libcrux_ml_dsa.Simd.Traits.f_repr ${rhs})
                    (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}));
            let pfk (k: nat{k < 8}) : Lemma
                (ensures
                    v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}) k) ==
                    v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig}) k) +
                    v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${rhs}) k)) =
                assert (mk_usize k <. Libcrux_ml_dsa.Simd.Traits.Specs.v_COEFFICIENTS_IN_SIMD_UNIT);
                assert (Libcrux_ml_dsa.Simd.Traits.Specs.int_is_i32
                    (v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig}) k) +
                     v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${rhs}) k)));
                Hacspec_ml_dsa.Commute.Chunk.lemma_add_lane_commute
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig}) k)
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${rhs}) k)
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}) k)
            in
            Classical.forall_intro pfk
        "#);
    }

    #[inline(always)]
    #[requires(specs::sub_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|_| specs::sub_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn subtract(lhs: &mut Self, rhs: &Self) {
        #[cfg(hax)]
        let _orig = *lhs;
        arithmetic::subtract(&mut lhs.value, &rhs.value);
        hax_lib::fstar!(r#"
            reveal_opaque (`%Libcrux_ml_dsa.Simd.Traits.Specs.sub_pre)
                (Libcrux_ml_dsa.Simd.Traits.Specs.sub_pre
                    (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig})
                    (Libcrux_ml_dsa.Simd.Traits.f_repr ${rhs}));
            reveal_opaque (`%Libcrux_ml_dsa.Simd.Traits.Specs.sub_post)
                (Libcrux_ml_dsa.Simd.Traits.Specs.sub_post
                    (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig})
                    (Libcrux_ml_dsa.Simd.Traits.f_repr ${rhs})
                    (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}));
            let pfk (k: nat{k < 8}) : Lemma
                (ensures
                    v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}) k) ==
                    v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig}) k) -
                    v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${rhs}) k)) =
                assert (mk_usize k <. Libcrux_ml_dsa.Simd.Traits.Specs.v_COEFFICIENTS_IN_SIMD_UNIT);
                assert (Libcrux_ml_dsa.Simd.Traits.Specs.int_is_i32
                    (v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig}) k) -
                     v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${rhs}) k)));
                Hacspec_ml_dsa.Commute.Chunk.lemma_sub_lane_commute
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${_orig}) k)
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${rhs}) k)
                    (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}) k)
            in
            Classical.forall_intro pfk
        "#);
    }

    #[inline(always)]
    #[requires(fstar!(r#"v $bound > 0 /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|result| fstar!(r#"
        Libcrux_ml_dsa.Simd.Traits.Specs.infinity_norm_exceeds_post
            (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) $bound $result"#))]
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool {
        infinity_norm_exceeds_with_proof(simd_unit, bound)
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|_| fstar!(r#"
        ((v $gamma2 == v ${crate::constants::GAMMA2_V95_232} ==>
            Spec.Utils.is_i32b_array_opaque 95232 (Libcrux_ml_dsa.Simd.Traits.f_repr ${low}_future)) /\
         (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} ==>
            Spec.Utils.is_i32b_array_opaque 261888 (Libcrux_ml_dsa.Simd.Traits.f_repr ${low}_future))) /\
        ((v $gamma2 == v ${crate::constants::GAMMA2_V95_232} ==>
            Spec.Utils.is_i32b_array_opaque 44 (Libcrux_ml_dsa.Simd.Traits.f_repr ${high}_future)) /\
         (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} ==>
            Spec.Utils.is_i32b_array_opaque 16 (Libcrux_ml_dsa.Simd.Traits.f_repr ${high}_future))) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.decompose_lane_post
            $gamma2
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${low}_future) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${high}_future) i))"#))]
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self) {
        hax_lib::fstar!("admit ()");
        arithmetic::decompose(gamma2, &simd_unit.value, &mut low.value, &mut high.value);
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${low}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${high})"#))]
    #[ensures(|result| fstar!(r#"v $result <= 8 /\
        Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque
          (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint}_future) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.compute_hint_lane_post
            $gamma2
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${low}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${high}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint}_future) i))"#))]
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize {
        hax_lib::fstar!("admit ()");
        arithmetic::compute_hint(&low.value, &high.value, gamma2, &mut hint.value)
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) /\
        Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint})"#))]
    #[ensures(|_| fstar!(r#"
        ((v $gamma2 == v ${crate::constants::GAMMA2_V95_232} ==>
            Spec.Utils.is_i32b_array_opaque 44 (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint}_future)) /\
         (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} ==>
            Spec.Utils.is_i32b_array_opaque 16 (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint}_future))) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.use_hint_lane_post
            $gamma2
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${hint}_future) i))"#))]
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self) {
        hax_lib::fstar!("admit ()");
        arithmetic::use_hint(gamma2, &simd_unit.value, &mut hint.value);
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (${rhs.repr()})"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}_future) /\
        Spec.MLDSA.Math.(forall i. i < 8 ==>
            mod_q (v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}_future) i)) ==
            mod_q (v (Seq.index (${lhs.repr()}) i) * v (Seq.index (${rhs.repr()}) i) * 8265825)) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.montgomery_multiply_lane_post
            (Seq.index (${lhs.repr()}) i)
            (Seq.index (${rhs.repr()}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${lhs}_future) i))"#))]
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self) {
        hax_lib::fstar!("admit ()");
        arithmetic::montgomery_multiply(&mut lhs.value, &rhs.value);
    }

    #[inline(always)]
    #[requires(fstar!(r#"v $SHIFT_BY == 13 /\
        (forall i. i < 8 ==> v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i) >= 0 /\
            v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i) <= 261631)"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.shift_left_then_reduce_lane_post
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}_future) i))"#))]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self) {
        shift_left_then_reduce_with_proof::<SHIFT_BY>(simd_unit)
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0})"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (pow2 12) (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}_future) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}_future) i) >= 0 /\
          v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}_future) i) < pow2 10) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.power2round_lane_post
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t1}_future) i)
            (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${t0}_future) i))"#))]
    fn power2round(t0: &mut Self, t1: &mut Self) {
        power2round_with_proof(t0, t1)
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        Seq.length $randomness / 3 <= 4294967295 /\
        Seq.length $randomness / 3 <= Seq.length $out"#))]
    #[ensures(|result| fstar!(r#"v $result <= 8 /\
        (forall (i:nat{i < Seq.length ${out}_future}). i < v $result ==>
          v (Seq.index ${out}_future i) >= 0 /\
          v (Seq.index ${out}_future i) < 8380417)"#))]
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
        hax_lib::fstar!("admit ()");
        rejection_sample::less_than_field_modulus::sample(randomness, out)
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        Seq.length $randomness * 2 <= 4294967295 /\
        Seq.length $randomness * 2 <= Seq.length $out"#))]
    #[ensures(|result| fstar!(r#"v $result <= 8 /\
        (forall (i:nat{i < Seq.length ${out}_future}). i < v $result ==>
          v (Seq.index ${out}_future i) >= -2 /\ v (Seq.index ${out}_future i) <= 2)"#))]
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize {
        hax_lib::fstar!("admit ()");
        rejection_sample::less_than_eta::sample::<2>(randomness, out)
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        Seq.length $randomness * 2 <= 4294967295 /\
        Seq.length $randomness * 2 <= Seq.length $out"#))]
    #[ensures(|result| fstar!(r#"v $result <= 8 /\
        (forall (i:nat{i < Seq.length ${out}_future}). i < v $result ==>
          v (Seq.index ${out}_future i) >= -4 /\ v (Seq.index ${out}_future i) <= 4)"#))]
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize {
        hax_lib::fstar!("admit ()");
        rejection_sample::less_than_eta::sample::<4>(randomness, out)
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        (v $gamma1_exponent == 17 \/ v $gamma1_exponent == 19) /\
        Seq.length $serialized == 1 + v $gamma1_exponent /\
        Spec.Utils.is_i32b_array_opaque (pow2 (v $gamma1_exponent)) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|_| fstar!(r#"
        Seq.length ${serialized}_future == Seq.length ${serialized}"#))]
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize) {
        hax_lib::fstar!("admit ()");
        encoding::gamma1::serialize(&simd_unit.value, serialized, gamma1_exponent)
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        (v $gamma1_exponent == 17 \/ v $gamma1_exponent == 19) /\
        Seq.length $serialized == 1 + v $gamma1_exponent"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (pow2 (v $gamma1_exponent))
          (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future)"#))]
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self, gamma1_exponent: usize) {
        hax_lib::fstar!("admit ()");
        encoding::gamma1::deserialize(serialized, &mut out.value, gamma1_exponent);
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        (Seq.length $serialized == 4 \/ Seq.length $serialized == 6) /\
        Spec.Utils.is_i32b_array_opaque (pow2 (Seq.length $serialized)) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|_| fstar!(r#"
        Seq.length ${serialized}_future == Seq.length ${serialized}"#))]
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [u8]) {
        hax_lib::fstar!("admit ()");
        encoding::commitment::serialize(&simd_unit.value, serialized)
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        Seq.length $serialized == (match $eta with
                                   | Libcrux_ml_dsa.Constants.Eta_Two -> 3
                                   | Libcrux_ml_dsa.Constants.Eta_Four -> 4) /\
        Spec.Utils.is_i32b_array_opaque (match $eta with
                                         | Libcrux_ml_dsa.Constants.Eta_Two -> 2
                                         | Libcrux_ml_dsa.Constants.Eta_Four -> 4)
                                        (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|_| fstar!(r#"
        Seq.length ${serialized}_future == Seq.length ${serialized}"#))]
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [u8]) {
        hax_lib::fstar!("admit ()");
        encoding::error::serialize(eta, &simd_unit.value, serialized)
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        Seq.length $serialized == (match $eta with
                                   | Libcrux_ml_dsa.Constants.Eta_Two -> 3
                                   | Libcrux_ml_dsa.Constants.Eta_Four -> 4)"#))]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          ($eta == Libcrux_ml_dsa.Constants.Eta_Two ==>
              v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) >= -2 /\
              v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) <= 2) /\
          ($eta == Libcrux_ml_dsa.Constants.Eta_Four ==>
              v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) >= -4 /\
              v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) <= 4))"#))]
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self) {
        hax_lib::fstar!("admit ()");
        encoding::error::deserialize(eta, serialized, &mut out.value);
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        Seq.length $out == 13 /\
        Spec.Utils.is_i32b_array_opaque (pow2 13) (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit})"#))]
    #[ensures(|_| fstar!(r#"
        Seq.length ${out}_future == Seq.length ${out}"#))]
    fn t0_serialize(simd_unit: &Self, out: &mut [u8]) {
        hax_lib::fstar!("admit ()");
        encoding::t0::serialize(&simd_unit.value, out);
    }

    #[inline(always)]
    #[requires(serialized.len() == 13)]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (pow2 12)
          (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future)"#))]
    fn t0_deserialize(serialized: &[u8], out: &mut Self) {
        hax_lib::fstar!("admit ()");
        encoding::t0::deserialize(serialized, &mut out.value);
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        Seq.length $out == 10 /\
        (forall (i: nat). i < 8 ==>
          v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i) >= 0 /\
          v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${simd_unit}) i) < pow2 10)"#))]
    #[ensures(|_| fstar!(r#"
        Seq.length ${out}_future == Seq.length ${out}"#))]
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]) {
        hax_lib::fstar!("admit ()");
        encoding::t1::serialize(&simd_unit.value, out);
    }

    #[inline(always)]
    #[requires(serialized.len() == 10)]
    #[ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) >= 0 /\
          v (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr ${out}_future) i) < pow2 10)"#))]
    fn t1_deserialize(serialized: &[u8], out: &mut Self) {
        hax_lib::fstar!("admit ()");
        encoding::t1::deserialize(serialized, &mut out.value);
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        (forall (i:nat). i < 32 ==>
            Spec.Utils.is_i32b_array_opaque
            (v ${specs::NTT_BASE_BOUND})
            (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} i)))
    "#))]
    #[ensures(|_| fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units}_future i)))
    "#))]
    fn ntt(simd_units: &mut AVX2RingElement) {
        hax_lib::fstar!("admit ()");
        ntt::ntt(simd_units);
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} i)))
    "#))]
    #[ensures(|_| fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units}_future i)))
    "#))]
    fn invert_ntt_montgomery(simd_units: &mut AVX2RingElement) {
        hax_lib::fstar!("admit ()");
        invntt::invert_ntt_montgomery(simd_units);
    }

    #[inline(always)]
    #[requires(fstar!(r#"
        (forall (i:nat). i < 32 ==>
            Spec.Utils.is_i32b_array_opaque 2143289343
                (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} i)))"#))]
    #[ensures(|_| fstar!(r#"
        (forall (j:nat). j < 32 ==>
          Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units}_future j)) /\
          Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
            Libcrux_ml_dsa.Simd.Traits.Specs.reduce_lane_post
              (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units} j)) i)
              (Seq.index (Libcrux_ml_dsa.Simd.Traits.f_repr (Seq.index ${simd_units}_future j)) i)))"#))]
    fn reduce(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]) {
        reduce_with_proof(simd_units)
    }
}
