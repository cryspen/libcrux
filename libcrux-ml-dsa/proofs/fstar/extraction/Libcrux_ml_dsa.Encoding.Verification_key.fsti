module Libcrux_ml_dsa.Encoding.Verification_key
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val deserialize
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (rows_in_a verification_key_size: usize)
      (serialized: t_Slice u8)
      (t1: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

val generate_serialized
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (seed: t_Slice u8)
      (t1: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (verification_key_serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
