module Libcrux_ml_dsa.Encoding.Signature
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val set_hint (out_hint: t_Slice (t_Array i32 (sz 256))) (i j: usize)
    : Prims.Pure (t_Slice (t_Array i32 (sz 256))) Prims.l_True (fun _ -> Prims.l_True)

val deserialize
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (columns_in_a rows_in_a commitment_hash_size gamma1_exponent gamma1_ring_element_size max_ones_in_hint signature_size:
          usize)
      (serialized out_commitment_hash: t_Slice u8)
      (out_signer_response: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (out_hint: t_Slice (t_Array i32 (sz 256)))
    : Prims.Pure
      (t_Slice u8 & t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
        t_Slice (t_Array i32 (sz 256)) &
        Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (commitment_hash: t_Slice u8)
      (signer_response: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (hint: t_Slice (t_Array i32 (sz 256)))
      (commitment_hash_size columns_in_a rows_in_a gamma1_exponent gamma1_ring_element_size max_ones_in_hint:
          usize)
      (signature: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
