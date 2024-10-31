module Libcrux_ml_dsa.Simd.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val add (lhs rhs: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val compute_hint (v_GAMMA2: i32) (low high: u8)
    : Prims.Pure (usize & u8) Prims.l_True (fun _ -> Prims.l_True)

val infinity_norm_exceeds (simd_unit: u8) (bound: i32)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val subtract (lhs rhs: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val shift_left_then_reduce (v_SHIFT_BY: i32) (simd_unit: u8)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val to_unsigned_representatives (t: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val power2round (r: u8) : Prims.Pure (u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply (lhs rhs: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant (lhs: u8) (constant: i32)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val decompose (v_GAMMA2: i32) (r: u8) : Prims.Pure (u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val use_hint (v_GAMMA2: i32) (r hint: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
