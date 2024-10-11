module Libcrux_ml_dsa.Encoding.Verification_key
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val generate_serialized
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_VERIFICATION_KEY_SIZE: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (seed_for_A: t_Slice u8)
      (t1: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
    : Prims.Pure (t_Array u8 v_VERIFICATION_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val deserialize
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_VERIFICATION_KEY_SIZE: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
    : Prims.Pure
      (t_Array u8 (Rust_primitives.mk_usize 32) &
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
      Prims.l_True
      (fun _ -> Prims.l_True)
