module Libcrux_ml_dsa.Sample_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

(* ============================================================================
   Hand-written companion for `src/sample.rs` (annotation-uniformity sweep
   Batch 1).  Relocated from the `sample_mask_ring_element` fstar::before
   block.  This module is NOT generated -- edit it directly.
   ========================================================================== *)

(* Lift `gamma1::deserialize`'s per-simd-unit `is_i32b_array_opaque (pow2
   gamma1_exponent)` post (gamma1_exponent ∈ {17,19}) to the uniform
   `is_bounded_poly 8380416` bound that `ntt` / `compute_matrix_x_mask`
   expect on the mask: `pow2 17 = 131072` and `pow2 19 = 524288` are both
   `<= 8380416` (FIELD_MODULUS - 1).  Consumers: Sample.fst
   (sample_mask_ring_element / sample_mask_vector proof! blocks). *)
let lemma_gamma1_deser_widen
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (gamma1_exponent: usize)
      (result: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Lemma
      (requires
        (v gamma1_exponent == 17 \/ v gamma1_exponent == 19) /\
        (forall (j: nat). j < 32 ==>
           Spec.Utils.is_i32b_array_opaque (pow2 (v gamma1_exponent))
             (i0._super_i2.f_repr (Seq.index result.Libcrux_ml_dsa.Polynomial.f_simd_units j))))
      (ensures Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly (mk_usize 8380416) result)
  = let aux (j: nat{j < 32}) :
      Lemma (Spec.Utils.is_i32b_array_opaque 8380416
               (i0._super_i2.f_repr (Seq.index result.Libcrux_ml_dsa.Polynomial.f_simd_units j))) =
      assert_norm (pow2 17 <= 8380416);
      assert_norm (pow2 19 <= 8380416);
      Spec.Utils.is_i32b_array_larger (pow2 (v gamma1_exponent)) 8380416
        (i0._super_i2.f_repr (Seq.index result.Libcrux_ml_dsa.Polynomial.f_simd_units j))
    in
    Classical.forall_intro aux;
    Libcrux_ml_dsa.Polynomial.Spec.lemma_is_bounded_poly_intro (mk_usize 8380416) result
