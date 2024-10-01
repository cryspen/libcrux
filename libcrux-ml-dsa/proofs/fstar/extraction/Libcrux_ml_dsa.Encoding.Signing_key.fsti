module Libcrux_ml_dsa.Encoding.Signing_key
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val generate_serialized
      (#v_SIMDUnit #v_Shake256: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256 |}
      (seed_for_A seed_for_signing verification_key: t_Slice u8)
      (s1: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      (s2 t0: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
    : Prims.Pure (t_Array u8 v_SIGNING_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_then_ntt
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (serialized: t_Array u8 v_SIGNING_KEY_SIZE)
    : Prims.Pure
      (t_Array u8 (sz 32) & t_Array u8 (sz 32) & t_Array u8 (sz 64) &
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A &
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A &
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
      Prims.l_True
      (fun _ -> Prims.l_True)
