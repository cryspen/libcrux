module Libcrux_ml_kem.Vector.Neon.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BARRETT_MULTIPLIER: i16 = 20159s

val barrett_reduce_int16x8_t (v: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_reduce_int16x8_t (low high: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant_int16x8_t (v: u8) (c: i16)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_int16x8_t (v c: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val add (lhs rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val barrett_reduce (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val bitwise_and_with_constant (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val cond_subtract_3329_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant
      (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val multiply_by_constant (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val shift_right (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val sub (lhs rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)
