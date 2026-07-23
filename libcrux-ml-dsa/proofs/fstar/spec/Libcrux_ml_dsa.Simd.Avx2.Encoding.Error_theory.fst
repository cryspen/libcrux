module Libcrux_ml_dsa.Simd.Avx2.Encoding.Error_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models
open Spec.Intrinsics

(* ============================================================================
   Hand-written companion for `src/simd/avx2/encoding/error.rs` (annotation-
   uniformity sweep Batch 2).  Relocated spec predicates for the eta
   deserialization contracts.  This module is NOT generated -- edit directly.
   ========================================================================== *)

let deserialize_to_unsigned_post
  (eta: Libcrux_ml_dsa.Constants.t_Eta)
  (serialized: t_Slice u8{Seq.length serialized == (match eta with | Libcrux_ml_dsa.Constants.Eta_Two  -> 3 | Libcrux_ml_dsa.Constants.Eta_Four -> 4)})
  (result: bv256)
  = let bytes = Seq.length serialized in
    (forall (i: nat{i < bytes * 8}).
       u8_to_bv serialized.[ mk_usize (i / 8) ] (mk_int (i % 8)) ==
       result.(mk_int ((i / bytes) * 32 + i % bytes))) /\
    (forall (i: nat{i < 256}).
       i % 32 >= bytes ==> Libcrux_core_models.Abstractions.Bit.Bit_Zero? result.(mk_int i))

module C = Libcrux_ml_dsa.Constants
let deserialize_post (eta: C.t_Eta)
         (serialized: t_Slice u8 {Seq.length serialized == (match eta with | C.Eta_Two  -> 3 | C.Eta_Four -> 4)})
         (result: bv256)
    = let eta_i32:i32 = match eta <: C.t_Eta with | C.Eta_Two  -> mk_i32 2 | C.Eta_Four -> mk_i32 4 in
      let bytes = Seq.length serialized in
      (forall i. v (to_i32x8 result i) > minint I32)
    /\ ( let out_reverted = mk_i32x8 (fun i -> neg (to_i32x8 result i) `add_mod` eta_i32) in
        deserialize_to_unsigned_post eta serialized out_reverted)
