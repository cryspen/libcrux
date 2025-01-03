module Libcrux_ml_dsa.Simd.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_intrinsics.Avx2_extract in
  ()

val add (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val compute_hint (v_GAMMA2: i32) (low high hint: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (Libcrux_intrinsics.Avx2_extract.t_Vec256 & usize)
      Prims.l_True
      (fun _ -> Prims.l_True)

val infinity_norm_exceeds (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (bound: i32)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val subtract (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val shift_left_then_reduce (v_SHIFT_BY: i32) (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val to_unsigned_representatives (t: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val decompose
      (gamma2: Libcrux_ml_dsa.Constants.t_Gamma2)
      (r r0 r1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure
      (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)
      Prims.l_True
      (fun _ -> Prims.l_True)

val power2round (r0 r1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure
      (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)
      Prims.l_True
      (fun _ -> Prims.l_True)

val use_hint
      (gamma2: Libcrux_ml_dsa.Constants.t_Gamma2)
      (r hint: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i32)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
