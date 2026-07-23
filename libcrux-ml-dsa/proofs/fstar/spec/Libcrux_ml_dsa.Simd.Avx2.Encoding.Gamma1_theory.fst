module Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models
open Spec.Intrinsics

(* ============================================================================
   Hand-written companion for `src/simd/avx2/encoding/gamma1.rs` (annotation-
   uniformity sweep Batch 2).  Relocated: the weaker-hypothesis
   mm256_add_epi64 SMTPat wrapper (fires in the serialize aux proofs).
   Gamma1.fst cites nothing here by name, so the host carries an
   `open Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1_theory` directive to create
   the dependency that loads this SMTPat.  NOT generated -- edit directly.
   ========================================================================== *)

let lemma_mm256_add_epi64_lemma_weaker lhs rhs (i: u64 {v i < 256})
  : Lemma
    (requires forall i. Libcrux_core_models.Abstractions.Bit.Bit_Zero? lhs.(i) \/ Libcrux_core_models.Abstractions.Bit.Bit_Zero? rhs.(i))
    (ensures (Libcrux_core_models.Abstractions.Bit.Bit_Zero? lhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == rhs.(i))
           /\ (Libcrux_core_models.Abstractions.Bit.Bit_Zero? rhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == lhs.(i)))
    [SMTPat (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i)]
    = Spec.Intrinsics.mm256_add_epi64_lemma lhs rhs i
