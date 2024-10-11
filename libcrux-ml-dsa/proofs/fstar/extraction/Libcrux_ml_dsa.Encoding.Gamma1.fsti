module Libcrux_ml_dsa.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let serialize__OUTPUT_BYTES_PER_SIMD_UNIT: usize = Rust_primitives.mk_usize 18

let serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1: usize = Rust_primitives.mk_usize 20

val serialize
      (#v_SIMDUnit: Type0)
      (v_GAMMA1_EXPONENT v_OUTPUT_BYTES: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (t_Array u8 v_OUTPUT_BYTES) Prims.l_True (fun _ -> Prims.l_True)

val deserialize
      (#v_SIMDUnit: Type0)
      (v_GAMMA1_EXPONENT: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)
