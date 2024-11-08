module Libcrux_ml_dsa.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let serialize__OUTPUT_BYTES_PER_SIMD_UNIT: usize = sz 4

let serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1: usize = sz 6

val serialize
      (#v_SIMDUnit: Type0)
      (v_OUTPUT_SIZE: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val serialize_vector
      (#v_SIMDUnit: Type0)
      (v_DIMENSION v_RING_ELEMENT_SIZE v_OUTPUT_SIZE: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (vector: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)
