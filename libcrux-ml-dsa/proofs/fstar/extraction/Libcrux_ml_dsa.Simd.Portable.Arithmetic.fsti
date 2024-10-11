module Libcrux_ml_dsa.Simd.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let v_MONTGOMERY_SHIFT: u8 = Rust_primitives.mk_u8 32

val compute_one_hint (v_GAMMA2 low high: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val get_n_least_significant_bits (n: u8) (value: u64)
    : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val reduce_element (fe: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_reduce_element (value: i64) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_fe_by_fer (fe fer: i32)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val decompose_element (v_GAMMA2 r: i32)
    : Prims.Pure (i32 & i32) Prims.l_True (fun _ -> Prims.l_True)

val power2round_element (t: i32) : Prims.Pure (i32 & i32) Prims.l_True (fun _ -> Prims.l_True)

val use_one_hint (v_GAMMA2 r hint: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val infinity_norm_exceeds (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit) (bound: i32)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (c: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val add (lhs rhs: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val compute_hint (v_GAMMA2: i32) (low high: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure (usize & Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val decompose (v_GAMMA2: i32) (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure
      (Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit &
        Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit) Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply (lhs rhs: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val power2round (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure
      (Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit &
        Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit) Prims.l_True (fun _ -> Prims.l_True)

val shift_left_then_reduce
      (v_SHIFT_BY: i32)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val subtract (lhs rhs: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val use_hint (v_GAMMA2: i32) (simd_unit hint: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)
