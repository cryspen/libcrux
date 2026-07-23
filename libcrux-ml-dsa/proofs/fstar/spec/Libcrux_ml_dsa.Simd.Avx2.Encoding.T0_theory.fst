module Libcrux_ml_dsa.Simd.Avx2.Encoding.T0_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models
open Spec.Intrinsics

(* ============================================================================
   Hand-written companion for `src/simd/avx2/encoding/t0.rs` (annotation-
   uniformity sweep Batch 2).  Relocated: the mm256_add_epi64 SMTPat wrapper
   (fires in `serialize_aux`'s proof -- in scope because T0.fst depends on
   this module) and the unsigned-deserialization spec predicate.  The
   `deserialize_post` predicate stays host-side: it cites the hax-mangled
   `v_POW_2_BITS_IN_LOWER_PART_OF_T_MINUS_ONE` (locked(own-const)).
   This module is NOT generated -- edit it directly.
   ========================================================================== *)

let mm256_add_epi64_lemma_smtpat lhs rhs (i: u64 {v i < 256})
  : Lemma
    (requires
      forall (j:nat{j < v i % 64}). Libcrux_core_models.Abstractions.Bit.Bit_Zero? lhs.(mk_int ((v i / 64) * 64 + j))
                         \/ Libcrux_core_models.Abstractions.Bit.Bit_Zero? rhs.(mk_int ((v i / 64) * 64 + j))
    )
    (ensures
      (Libcrux_core_models.Abstractions.Bit.Bit_Zero? lhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == rhs.(i)) /\
      (Libcrux_core_models.Abstractions.Bit.Bit_Zero? rhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == lhs.(i))
    )
    [SMTPat (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i)]
    = mm256_add_epi64_lemma lhs rhs i

let deserialize_unsigned_post
  (serialized: t_Slice u8{Seq.length serialized == 13})
  (result: bv256)
  = let bytes = 13 in
    (forall (i: nat{i < bytes * 8}).
       u8_to_bv serialized.[ mk_usize (i / 8) ] (mk_int (i % 8)) ==
       result.(mk_int ((i / bytes) * 32 + i % bytes))) /\
    (forall (i: nat{i < 256}).
       i % 32 >= bytes ==> Libcrux_core_models.Abstractions.Bit.Bit_Zero? result.(mk_int i))
