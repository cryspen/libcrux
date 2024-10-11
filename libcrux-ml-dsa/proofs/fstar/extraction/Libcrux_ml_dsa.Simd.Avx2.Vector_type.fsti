module Libcrux_ml_dsa.Simd.Avx2.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

type t_AVX2SIMDUnit = { f_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From t_AVX2SIMDUnit Libcrux_intrinsics.Avx2_extract.t_Vec256 =
  {
    f_from_pre = (fun (coefficients: Libcrux_intrinsics.Avx2_extract.t_Vec256) -> true);
    f_from_post
    =
    (fun (coefficients: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_AVX2SIMDUnit) -> true);
    f_from
    =
    fun (coefficients: Libcrux_intrinsics.Avx2_extract.t_Vec256) ->
      { f_coefficients = coefficients } <: t_AVX2SIMDUnit
  }

val v_ZERO: Prims.unit -> Prims.Pure t_AVX2SIMDUnit Prims.l_True (fun _ -> Prims.l_True)

val from_coefficient_array (coefficient_array: t_Slice i32)
    : Prims.Pure t_AVX2SIMDUnit Prims.l_True (fun _ -> Prims.l_True)

val to_coefficient_array (x: t_AVX2SIMDUnit)
    : Prims.Pure (t_Array i32 (Rust_primitives.mk_usize 8)) Prims.l_True (fun _ -> Prims.l_True)
