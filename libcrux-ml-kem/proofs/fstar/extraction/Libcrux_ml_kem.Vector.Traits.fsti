module Libcrux_ml_kem.Vector.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Operations (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11581440318597584651:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9442900250278684536:Core.Clone.t_Clone v_Self;
  f_ZERO_pre:Prims.unit -> Type0;
  f_ZERO_post:Prims.unit -> v_Self -> Type0;
  f_ZERO:x0: Prims.unit -> Prims.Pure v_Self (f_ZERO_pre x0) (fun result -> f_ZERO_post x0 result);
  f_from_i16_array_pre:t_Slice i16 -> Type0;
  f_from_i16_array_post:t_Slice i16 -> v_Self -> Type0;
  f_from_i16_array:x0: t_Slice i16
    -> Prims.Pure v_Self (f_from_i16_array_pre x0) (fun result -> f_from_i16_array_post x0 result);
  f_to_i16_array_pre:v_Self -> Type0;
  f_to_i16_array_post:v_Self -> t_Array i16 (sz 16) -> Type0;
  f_to_i16_array:x0: v_Self
    -> Prims.Pure (t_Array i16 (sz 16))
        (f_to_i16_array_pre x0)
        (fun result -> f_to_i16_array_post x0 result);
  f_add_pre:v_Self -> v_Self -> Type0;
  f_add_post:v_Self -> v_Self -> v_Self -> Type0;
  f_add:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result);
  f_sub_pre:v_Self -> v_Self -> Type0;
  f_sub_post:v_Self -> v_Self -> v_Self -> Type0;
  f_sub:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_sub_pre x0 x1) (fun result -> f_sub_post x0 x1 result);
  f_multiply_by_constant_pre:v_Self -> i16 -> Type0;
  f_multiply_by_constant_post:v_Self -> i16 -> v_Self -> Type0;
  f_multiply_by_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_multiply_by_constant_pre x0 x1)
        (fun result -> f_multiply_by_constant_post x0 x1 result);
  f_bitwise_and_with_constant_pre:v_Self -> i16 -> Type0;
  f_bitwise_and_with_constant_post:v_Self -> i16 -> v_Self -> Type0;
  f_bitwise_and_with_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_bitwise_and_with_constant_pre x0 x1)
        (fun result -> f_bitwise_and_with_constant_post x0 x1 result);
  f_shift_right_pre:v_SHIFT_BY: i32 -> v_Self -> Type0;
  f_shift_right_post:v_SHIFT_BY: i32 -> v_Self -> v_Self -> Type0;
  f_shift_right:v_SHIFT_BY: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_shift_right_pre v_SHIFT_BY x0)
        (fun result -> f_shift_right_post v_SHIFT_BY x0 result);
  f_cond_subtract_3329_pre:v_Self -> Type0;
  f_cond_subtract_3329_post:v_Self -> v_Self -> Type0;
  f_cond_subtract_3329_:x0: v_Self
    -> Prims.Pure v_Self
        (f_cond_subtract_3329_pre x0)
        (fun result -> f_cond_subtract_3329_post x0 result);
  f_barrett_reduce_pre:v_Self -> Type0;
  f_barrett_reduce_post:v_Self -> v_Self -> Type0;
  f_barrett_reduce:x0: v_Self
    -> Prims.Pure v_Self (f_barrett_reduce_pre x0) (fun result -> f_barrett_reduce_post x0 result);
  f_montgomery_multiply_by_constant_pre:v_Self -> i16 -> Type0;
  f_montgomery_multiply_by_constant_post:v_Self -> i16 -> v_Self -> Type0;
  f_montgomery_multiply_by_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_montgomery_multiply_by_constant_pre x0 x1)
        (fun result -> f_montgomery_multiply_by_constant_post x0 x1 result);
  f_compress_1_pre:v_Self -> Type0;
  f_compress_1_post:v_Self -> v_Self -> Type0;
  f_compress_1_:x0: v_Self
    -> Prims.Pure v_Self (f_compress_1_pre x0) (fun result -> f_compress_1_post x0 result);
  f_compress_pre:v_COEFFICIENT_BITS: i32 -> v_Self -> Type0;
  f_compress_post:v_COEFFICIENT_BITS: i32 -> v_Self -> v_Self -> Type0;
  f_compress:v_COEFFICIENT_BITS: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_compress_pre v_COEFFICIENT_BITS x0)
        (fun result -> f_compress_post v_COEFFICIENT_BITS x0 result);
  f_decompress_ciphertext_coefficient_pre:v_COEFFICIENT_BITS: i32 -> v_Self -> Type0;
  f_decompress_ciphertext_coefficient_post:v_COEFFICIENT_BITS: i32 -> v_Self -> v_Self -> Type0;
  f_decompress_ciphertext_coefficient:v_COEFFICIENT_BITS: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_decompress_ciphertext_coefficient_pre v_COEFFICIENT_BITS x0)
        (fun result -> f_decompress_ciphertext_coefficient_post v_COEFFICIENT_BITS x0 result);
  f_ntt_layer_1_step_pre:v_Self -> i16 -> i16 -> i16 -> i16 -> Type0;
  f_ntt_layer_1_step_post:v_Self -> i16 -> i16 -> i16 -> i16 -> v_Self -> Type0;
  f_ntt_layer_1_step:x0: v_Self -> x1: i16 -> x2: i16 -> x3: i16 -> x4: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_1_step_pre x0 x1 x2 x3 x4)
        (fun result -> f_ntt_layer_1_step_post x0 x1 x2 x3 x4 result);
  f_ntt_layer_2_step_pre:v_Self -> i16 -> i16 -> Type0;
  f_ntt_layer_2_step_post:v_Self -> i16 -> i16 -> v_Self -> Type0;
  f_ntt_layer_2_step:x0: v_Self -> x1: i16 -> x2: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_2_step_pre x0 x1 x2)
        (fun result -> f_ntt_layer_2_step_post x0 x1 x2 result);
  f_ntt_layer_3_step_pre:v_Self -> i16 -> Type0;
  f_ntt_layer_3_step_post:v_Self -> i16 -> v_Self -> Type0;
  f_ntt_layer_3_step:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_3_step_pre x0 x1)
        (fun result -> f_ntt_layer_3_step_post x0 x1 result);
  f_inv_ntt_layer_1_step_pre:v_Self -> i16 -> i16 -> i16 -> i16 -> Type0;
  f_inv_ntt_layer_1_step_post:v_Self -> i16 -> i16 -> i16 -> i16 -> v_Self -> Type0;
  f_inv_ntt_layer_1_step:x0: v_Self -> x1: i16 -> x2: i16 -> x3: i16 -> x4: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_1_step_pre x0 x1 x2 x3 x4)
        (fun result -> f_inv_ntt_layer_1_step_post x0 x1 x2 x3 x4 result);
  f_inv_ntt_layer_2_step_pre:v_Self -> i16 -> i16 -> Type0;
  f_inv_ntt_layer_2_step_post:v_Self -> i16 -> i16 -> v_Self -> Type0;
  f_inv_ntt_layer_2_step:x0: v_Self -> x1: i16 -> x2: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_2_step_pre x0 x1 x2)
        (fun result -> f_inv_ntt_layer_2_step_post x0 x1 x2 result);
  f_inv_ntt_layer_3_step_pre:v_Self -> i16 -> Type0;
  f_inv_ntt_layer_3_step_post:v_Self -> i16 -> v_Self -> Type0;
  f_inv_ntt_layer_3_step:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_3_step_pre x0 x1)
        (fun result -> f_inv_ntt_layer_3_step_post x0 x1 result);
  f_ntt_multiply_pre:v_Self -> v_Self -> i16 -> i16 -> i16 -> i16 -> Type0;
  f_ntt_multiply_post:v_Self -> v_Self -> i16 -> i16 -> i16 -> i16 -> v_Self -> Type0;
  f_ntt_multiply:x0: v_Self -> x1: v_Self -> x2: i16 -> x3: i16 -> x4: i16 -> x5: i16
    -> Prims.Pure v_Self
        (f_ntt_multiply_pre x0 x1 x2 x3 x4 x5)
        (fun result -> f_ntt_multiply_post x0 x1 x2 x3 x4 x5 result);
  f_serialize_1_pre:v_Self -> Type0;
  f_serialize_1_post:v_Self -> t_Array u8 (sz 2) -> Type0;
  f_serialize_1_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 2))
        (f_serialize_1_pre x0)
        (fun result -> f_serialize_1_post x0 result);
  f_deserialize_1_pre:t_Slice u8 -> Type0;
  f_deserialize_1_post:t_Slice u8 -> v_Self -> Type0;
  f_deserialize_1_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_1_pre x0) (fun result -> f_deserialize_1_post x0 result);
  f_serialize_4_pre:v_Self -> Type0;
  f_serialize_4_post:v_Self -> t_Array u8 (sz 8) -> Type0;
  f_serialize_4_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 8))
        (f_serialize_4_pre x0)
        (fun result -> f_serialize_4_post x0 result);
  f_deserialize_4_pre:t_Slice u8 -> Type0;
  f_deserialize_4_post:t_Slice u8 -> v_Self -> Type0;
  f_deserialize_4_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_4_pre x0) (fun result -> f_deserialize_4_post x0 result);
  f_serialize_5_pre:v_Self -> Type0;
  f_serialize_5_post:v_Self -> t_Array u8 (sz 10) -> Type0;
  f_serialize_5_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 10))
        (f_serialize_5_pre x0)
        (fun result -> f_serialize_5_post x0 result);
  f_deserialize_5_pre:t_Slice u8 -> Type0;
  f_deserialize_5_post:t_Slice u8 -> v_Self -> Type0;
  f_deserialize_5_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_5_pre x0) (fun result -> f_deserialize_5_post x0 result);
  f_serialize_10_pre:v_Self -> Type0;
  f_serialize_10_post:v_Self -> t_Array u8 (sz 20) -> Type0;
  f_serialize_10_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 20))
        (f_serialize_10_pre x0)
        (fun result -> f_serialize_10_post x0 result);
  f_deserialize_10_pre:t_Slice u8 -> Type0;
  f_deserialize_10_post:t_Slice u8 -> v_Self -> Type0;
  f_deserialize_10_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_10_pre x0) (fun result -> f_deserialize_10_post x0 result);
  f_serialize_11_pre:v_Self -> Type0;
  f_serialize_11_post:v_Self -> t_Array u8 (sz 22) -> Type0;
  f_serialize_11_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 22))
        (f_serialize_11_pre x0)
        (fun result -> f_serialize_11_post x0 result);
  f_deserialize_11_pre:t_Slice u8 -> Type0;
  f_deserialize_11_post:t_Slice u8 -> v_Self -> Type0;
  f_deserialize_11_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_11_pre x0) (fun result -> f_deserialize_11_post x0 result);
  f_serialize_12_pre:v_Self -> Type0;
  f_serialize_12_post:v_Self -> t_Array u8 (sz 24) -> Type0;
  f_serialize_12_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 24))
        (f_serialize_12_pre x0)
        (fun result -> f_serialize_12_post x0 result);
  f_deserialize_12_pre:t_Slice u8 -> Type0;
  f_deserialize_12_post:t_Slice u8 -> v_Self -> Type0;
  f_deserialize_12_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_12_pre x0) (fun result -> f_deserialize_12_post x0 result);
  f_rej_sample_pre:t_Slice u8 -> t_Slice i16 -> Type0;
  f_rej_sample_post:t_Slice u8 -> t_Slice i16 -> (t_Slice i16 & usize) -> Type0;
  f_rej_sample:x0: t_Slice u8 -> x1: t_Slice i16
    -> Prims.Pure (t_Slice i16 & usize)
        (f_rej_sample_pre x0 x1)
        (fun result -> f_rej_sample_post x0 x1 result)
}

let v_FIELD_ELEMENTS_IN_VECTOR: usize = sz 16

let v_FIELD_MODULUS: i16 = 3329s

let v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209ul

let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353s

val decompress_1_ (#v_T: Type0) {| i1: t_Operations v_T |} (v: v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_fe (#v_T: Type0) {| i1: t_Operations v_T |} (v: v_T) (fer: i16)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val to_standard_domain (#v_T: Type0) {| i1: t_Operations v_T |} (v: v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val to_unsigned_representative (#v_T: Type0) {| i1: t_Operations v_T |} (a: v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)
