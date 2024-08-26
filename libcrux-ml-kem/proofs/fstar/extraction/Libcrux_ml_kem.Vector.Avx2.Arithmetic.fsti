module Libcrux_ml_kem.Vector.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BARRETT_MULTIPLIER: i16 = 20159s

val add (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result ==
          Spec.Utils.map2 ( +. )
            (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 lhs)
            (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 rhs))

val bitwise_and_with_constant (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val multiply_by_constant (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val shift_right (v_SHIFT_BY: i32) (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val sub (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

/// See Section 3.2 of the implementation notes document for an explanation
/// of this code.
val barrett_reduce (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val cond_subtract_3329_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (constant: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constants (v c: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_m128i_by_constants (v c: Libcrux_intrinsics.Avx2_extract.t_Vec128)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec128 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_reduce_i32s (v: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
