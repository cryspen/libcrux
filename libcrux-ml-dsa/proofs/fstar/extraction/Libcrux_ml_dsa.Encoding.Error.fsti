module Libcrux_ml_dsa.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let serialize__OUTPUT_BYTES_PER_SIMD_UNIT: usize = sz 3

let serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1: usize = sz 4

val deserialize
      (#v_SIMDUnit: Type0)
      (v_ETA: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_to_vector_then_ntt
      (#v_SIMDUnit: Type0)
      (v_DIMENSION v_ETA v_RING_ELEMENT_SIZE: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (serialized: t_Slice u8)
    : Prims.Pure
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize
      (#v_SIMDUnit: Type0)
      (v_ETA v_OUTPUT_SIZE: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)
