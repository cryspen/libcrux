module Libcrux_ml_kem.Simd.Simd256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compress_1___FIELD_MODULUS_HAVLED: i32 =
  (Libcrux_ml_kem.Constants.v_FIELD_MODULUS -! 1l <: i32) /! 2l

let compress_1___FIELD_MODULUS_QUARTERED: i32 =
  (Libcrux_ml_kem.Constants.v_FIELD_MODULUS -! 1l <: i32) /! 4l

type t_SIMD256Vector = { f_elements:Core.Core_arch.X86.t____m256i }

val impl__SIMD256Vector__add (self rhs: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val impl__SIMD256Vector__add_constant (self: t_SIMD256Vector) (c: i32)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val impl__SIMD256Vector__sub (self rhs: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val bitwise_and_with_constant (v: t_SIMD256Vector) (c: i32)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val compress_1_ (v: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val cond_subtract_3329_ (v: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_1_ (a: u8) : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_4_ (v: t_Slice u8) : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val from_i32_array (array: t_Array i32 (sz 8))
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val multiply_by_constant (v: t_SIMD256Vector) (c: i32)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val serialize_1_ (v: t_SIMD256Vector) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val serialize_4_ (v: t_SIMD256Vector)
    : Prims.Pure (t_Array u8 (sz 4)) Prims.l_True (fun _ -> Prims.l_True)

val shift_left (v_SHIFT_BY: i32) (v: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val shift_right (v_SHIFT_BY: i32) (v: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val to_i32_array (v: t_SIMD256Vector)
    : Prims.Pure (t_Array i32 (sz 8)) Prims.l_True (fun _ -> Prims.l_True)

val barrett_reduce (v: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val compress (v_COEFFICIENT_BITS: i32) (v: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_10_ (v: t_Slice u8)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_11_ (v: t_Slice u8)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_12_ (v: t_Slice u8)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_5_ (v: t_Slice u8) : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_1_step (v: t_SIMD256Vector) (zeta1 zeta2: i32)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_2_step (v: t_SIMD256Vector) (zeta: i32)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val montgomery_reduce (v: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_1_step (v: t_SIMD256Vector) (zeta1 zeta2: i32)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_2_step (v: t_SIMD256Vector) (zeta: i32)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val ntt_multiply (lhs rhs: t_SIMD256Vector) (zeta0 zeta1: i32)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val serialize_10_ (v: t_SIMD256Vector)
    : Prims.Pure (t_Array u8 (sz 10)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_11_ (v: t_SIMD256Vector)
    : Prims.Pure (t_Array u8 (sz 11)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_12_ (v: t_SIMD256Vector)
    : Prims.Pure (t_Array u8 (sz 12)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_5_ (v: t_SIMD256Vector)
    : Prims.Pure (t_Array u8 (sz 5)) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Libcrux_ml_kem.Simd.Simd_trait.t_Operations t_SIMD256Vector =
  {
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post = (fun (_: Prims.unit) (out: t_SIMD256Vector) -> true);
    f_ZERO
    =
    (fun (_: Prims.unit) ->
        { f_elements = Libcrux_ml_kem.Simd.Simd256.X64_avx2.zero () } <: t_SIMD256Vector);
    f_to_i32_array_pre = (fun (v: t_SIMD256Vector) -> true);
    f_to_i32_array_post = (fun (v: t_SIMD256Vector) (out: t_Array i32 (sz 8)) -> true);
    f_to_i32_array = (fun (v: t_SIMD256Vector) -> to_i32_array v);
    f_from_i32_array_pre = (fun (array: t_Array i32 (sz 8)) -> true);
    f_from_i32_array_post = (fun (array: t_Array i32 (sz 8)) (out: t_SIMD256Vector) -> true);
    f_from_i32_array = (fun (array: t_Array i32 (sz 8)) -> from_i32_array array);
    f_add_constant_pre = (fun (v: t_SIMD256Vector) (c: i32) -> true);
    f_add_constant_post = (fun (v: t_SIMD256Vector) (c: i32) (out: t_SIMD256Vector) -> true);
    f_add_constant = (fun (v: t_SIMD256Vector) (c: i32) -> impl__SIMD256Vector__add_constant v c);
    f_add_pre = (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) -> true);
    f_add_post = (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_add = (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) -> impl__SIMD256Vector__add lhs rhs);
    f_sub_pre = (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) -> true);
    f_sub_post = (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_sub = (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) -> impl__SIMD256Vector__sub lhs rhs);
    f_multiply_by_constant_pre = (fun (v: t_SIMD256Vector) (c: i32) -> true);
    f_multiply_by_constant_post = (fun (v: t_SIMD256Vector) (c: i32) (out: t_SIMD256Vector) -> true);
    f_multiply_by_constant = (fun (v: t_SIMD256Vector) (c: i32) -> multiply_by_constant v c);
    f_bitwise_and_with_constant_pre = (fun (v: t_SIMD256Vector) (c: i32) -> true);
    f_bitwise_and_with_constant_post
    =
    (fun (v: t_SIMD256Vector) (c: i32) (out: t_SIMD256Vector) -> true);
    f_bitwise_and_with_constant
    =
    (fun (v: t_SIMD256Vector) (c: i32) -> bitwise_and_with_constant v c);
    f_shift_right_pre = (fun (v_SHIFT_BY: i32) (v: t_SIMD256Vector) -> true);
    f_shift_right_post = (fun (v_SHIFT_BY: i32) (v: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_shift_right = (fun (v_SHIFT_BY: i32) (v: t_SIMD256Vector) -> shift_right v_SHIFT_BY v);
    f_shift_left_pre = (fun (v_SHIFT_BY: i32) (v: t_SIMD256Vector) -> true);
    f_shift_left_post = (fun (v_SHIFT_BY: i32) (v: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_shift_left = (fun (v_SHIFT_BY: i32) (v: t_SIMD256Vector) -> shift_left v_SHIFT_BY v);
    f_cond_subtract_3329_pre = (fun (v: t_SIMD256Vector) -> true);
    f_cond_subtract_3329_post = (fun (v: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_cond_subtract_3329_ = (fun (v: t_SIMD256Vector) -> cond_subtract_3329_ v);
    f_barrett_reduce_pre = (fun (v: t_SIMD256Vector) -> true);
    f_barrett_reduce_post = (fun (v: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_barrett_reduce = (fun (v: t_SIMD256Vector) -> barrett_reduce v);
    f_montgomery_reduce_pre = (fun (v: t_SIMD256Vector) -> true);
    f_montgomery_reduce_post = (fun (v: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_montgomery_reduce = (fun (v: t_SIMD256Vector) -> montgomery_reduce v);
    f_compress_1_pre = (fun (v: t_SIMD256Vector) -> true);
    f_compress_1_post = (fun (v: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_compress_1_ = (fun (v: t_SIMD256Vector) -> compress_1_ v);
    f_compress_pre = (fun (v_COEFFICIENT_BITS: i32) (v: t_SIMD256Vector) -> true);
    f_compress_post
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_compress
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: t_SIMD256Vector) -> compress v_COEFFICIENT_BITS v);
    f_ntt_layer_1_step_pre = (fun (a: t_SIMD256Vector) (zeta1: i32) (zeta2: i32) -> true);
    f_ntt_layer_1_step_post
    =
    (fun (a: t_SIMD256Vector) (zeta1: i32) (zeta2: i32) (out: t_SIMD256Vector) -> true);
    f_ntt_layer_1_step
    =
    (fun (a: t_SIMD256Vector) (zeta1: i32) (zeta2: i32) -> ntt_layer_1_step a zeta1 zeta2);
    f_ntt_layer_2_step_pre = (fun (a: t_SIMD256Vector) (zeta: i32) -> true);
    f_ntt_layer_2_step_post = (fun (a: t_SIMD256Vector) (zeta: i32) (out: t_SIMD256Vector) -> true);
    f_ntt_layer_2_step = (fun (a: t_SIMD256Vector) (zeta: i32) -> ntt_layer_2_step a zeta);
    f_inv_ntt_layer_1_step_pre = (fun (a: t_SIMD256Vector) (zeta1: i32) (zeta2: i32) -> true);
    f_inv_ntt_layer_1_step_post
    =
    (fun (a: t_SIMD256Vector) (zeta1: i32) (zeta2: i32) (out: t_SIMD256Vector) -> true);
    f_inv_ntt_layer_1_step
    =
    (fun (a: t_SIMD256Vector) (zeta1: i32) (zeta2: i32) -> inv_ntt_layer_1_step a zeta1 zeta2);
    f_inv_ntt_layer_2_step_pre = (fun (a: t_SIMD256Vector) (zeta: i32) -> true);
    f_inv_ntt_layer_2_step_post
    =
    (fun (a: t_SIMD256Vector) (zeta: i32) (out: t_SIMD256Vector) -> true);
    f_inv_ntt_layer_2_step = (fun (a: t_SIMD256Vector) (zeta: i32) -> inv_ntt_layer_2_step a zeta);
    f_ntt_multiply_pre
    =
    (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) (zeta0: i32) (zeta1: i32) -> true);
    f_ntt_multiply_post
    =
    (fun
        (lhs: t_SIMD256Vector)
        (rhs: t_SIMD256Vector)
        (zeta0: i32)
        (zeta1: i32)
        (out: t_SIMD256Vector)
        ->
        true);
    f_ntt_multiply
    =
    (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) (zeta0: i32) (zeta1: i32) ->
        ntt_multiply lhs rhs zeta0 zeta1);
    f_serialize_1_pre = (fun (a: t_SIMD256Vector) -> true);
    f_serialize_1_post = (fun (a: t_SIMD256Vector) (out: u8) -> true);
    f_serialize_1_ = (fun (a: t_SIMD256Vector) -> serialize_1_ a);
    f_deserialize_1_pre = (fun (a: u8) -> true);
    f_deserialize_1_post = (fun (a: u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_1_ = (fun (a: u8) -> deserialize_1_ a);
    f_serialize_4_pre = (fun (a: t_SIMD256Vector) -> true);
    f_serialize_4_post = (fun (a: t_SIMD256Vector) (out: t_Array u8 (sz 4)) -> true);
    f_serialize_4_ = (fun (a: t_SIMD256Vector) -> serialize_4_ a);
    f_deserialize_4_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_4_post = (fun (a: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_4_ = (fun (a: t_Slice u8) -> deserialize_4_ a);
    f_serialize_5_pre = (fun (a: t_SIMD256Vector) -> true);
    f_serialize_5_post = (fun (a: t_SIMD256Vector) (out: t_Array u8 (sz 5)) -> true);
    f_serialize_5_ = (fun (a: t_SIMD256Vector) -> serialize_5_ a);
    f_deserialize_5_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_5_post = (fun (a: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_5_ = (fun (a: t_Slice u8) -> deserialize_5_ a);
    f_serialize_10_pre = (fun (a: t_SIMD256Vector) -> true);
    f_serialize_10_post = (fun (a: t_SIMD256Vector) (out: t_Array u8 (sz 10)) -> true);
    f_serialize_10_ = (fun (a: t_SIMD256Vector) -> serialize_10_ a);
    f_deserialize_10_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_10_post = (fun (a: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_10_ = (fun (a: t_Slice u8) -> deserialize_10_ a);
    f_serialize_11_pre = (fun (a: t_SIMD256Vector) -> true);
    f_serialize_11_post = (fun (a: t_SIMD256Vector) (out: t_Array u8 (sz 11)) -> true);
    f_serialize_11_ = (fun (a: t_SIMD256Vector) -> serialize_11_ a);
    f_deserialize_11_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_11_post = (fun (a: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_11_ = (fun (a: t_Slice u8) -> deserialize_11_ a);
    f_serialize_12_pre = (fun (a: t_SIMD256Vector) -> true);
    f_serialize_12_post = (fun (a: t_SIMD256Vector) (out: t_Array u8 (sz 12)) -> true);
    f_serialize_12_ = (fun (a: t_SIMD256Vector) -> serialize_12_ a);
    f_deserialize_12_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_12_post = (fun (a: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_12_ = fun (a: t_Slice u8) -> deserialize_12_ a
  }
