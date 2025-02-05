module Libcrux_ml_kem.Vector.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

open Libcrux_intrinsics.Avx2_extract

val add (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        forall i.
          i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (get_lane lhs i) + v (get_lane rhs i)))
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          forall i. i < 16 ==> v (get_lane result i) == (v (get_lane lhs i) + v (get_lane rhs i)))

val sub (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        forall i.
          i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (get_lane lhs i) - v (get_lane rhs i)))
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          forall i. i < 16 ==> v (get_lane result i) == (v (get_lane lhs i) - v (get_lane rhs i)))

val multiply_by_constant (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        forall i. i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (get_lane vector i) * v constant))
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          forall i. i < 16 ==> v (get_lane result i) == (v (get_lane vector i) * v constant))

val bitwise_and_with_constant (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result ==
          Spec.Utils.map_array (fun x -> x &. constant)
            (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector))

val shift_right (v_SHIFT_BY: i32) (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 16)
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          (v_SHIFT_BY >=. (mk_i32 0) /\ v_SHIFT_BY <. (mk_i32 16)) ==>
          Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result ==
          Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY)
            (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector))

val cond_subtract_3329_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        Spec.Utils.is_i16b_array (pow2 12 - 1)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector))
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          forall i.
            i < 16 ==>
            get_lane result i ==
            (if (get_lane vector i) >=. (mk_i16 3329)
              then get_lane vector i -! (mk_i16 3329)
              else get_lane vector i))

let v_BARRETT_MULTIPLIER: i16 = mk_i16 20159

/// See Section 3.2 of the implementation notes document for an explanation
/// of this code.
val barrett_reduce (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        Spec.Utils.is_i16b_array 28296 (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector))
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          Spec.Utils.is_i16b_array 3328 (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result) /\
          (forall i. i < 16 ==> v (get_lane result i) % 3329 == (v (get_lane vector i) % 3329)))

val montgomery_multiply_by_constant
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (constant: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires Spec.Utils.is_i16b 1664 constant)
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          Spec.Utils.is_i16b_array 3328 (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result) /\
          (forall i.
              i < 16 ==>
              v (get_lane result i) % 3329 == ((v (get_lane vector i) * v constant * 169) % 3329)))

val montgomery_multiply_by_constants (vec constants: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        Spec.Utils.is_i16b_array 1664 (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 constants))
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          Spec.Utils.is_i16b_array 3328 (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result) /\
          (forall i.
              i < 16 ==>
              v (get_lane result i) % 3329 ==
              ((v (get_lane vec i) * v (get_lane constants i) * 169) % 3329)))

val montgomery_reduce_i32s (vec: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        Spec.Utils.is_i16b_array (3328 * pow2 16)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vec))
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          Spec.Utils.is_i16b_array (3328 + 1665)
            (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result) /\
          (Spec.Utils.is_i16b_array (3328 * pow2 15)
              (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vec) ==>
            Spec.Utils.is_i16b_array 3328 (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result)) /\
          (forall i. i < 16 ==> v (get_lane result i) % 3329 == ((v (get_lane vec i) * 169) % 3329))
      )

val montgomery_multiply_m128i_by_constants (vec constants: Libcrux_intrinsics.Avx2_extract.t_Vec128)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec128
      (requires
        Spec.Utils.is_i16b_array 1664 (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 constants))
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec128 = result in
          Spec.Utils.is_i16b_array 3328 (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 result) /\
          (forall i.
              i < 8 ==>
              v (get_lane128 result i) % 3329 ==
              ((v (get_lane128 vec i) * v (get_lane128 constants i) * 169) % 3329)))
