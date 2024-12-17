module Libcrux_ml_dsa.Encoding.Signature
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

/// A signature
/// This is only an internal type.
type t_Signature
  (v_SIMDUnit: Type0) (v_COMMITMENT_HASH_SIZE: usize) (v_COLUMNS_IN_A: usize) (v_ROWS_IN_A: usize)
  {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
  = {
  f_commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE;
  f_signer_response:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_COLUMNS_IN_A;
  f_hint:t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A
}

val impl__deserialize
      (#v_SIMDUnit: Type0)
      (v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_MAX_ONES_IN_HINT v_SIGNATURE_SIZE:
          usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (serialized: t_Array u8 v_SIGNATURE_SIZE)
    : Prims.Pure
      (Core.Result.t_Result
          (t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A)
          Libcrux_ml_dsa.Types.t_VerificationError) Prims.l_True (fun _ -> Prims.l_True)

val impl__serialize
      (#v_SIMDUnit: Type0)
      (v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_MAX_ONES_IN_HINT v_SIGNATURE_SIZE:
          usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (self: t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A)
    : Prims.Pure (t_Array u8 v_SIGNATURE_SIZE) Prims.l_True (fun _ -> Prims.l_True)
