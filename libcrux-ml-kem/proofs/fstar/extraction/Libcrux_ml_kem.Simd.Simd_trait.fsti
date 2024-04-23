module Libcrux_ml_kem.Simd.Simd_trait
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Operations (v_Self: Type) = {
  f_Vector:Type;
  f_Vector_15713626723705489010:Core.Marker.t_Copy f_Vector;
  f_Vector_8701872305793597044:Core.Clone.t_Clone f_Vector;
  f_FIELD_ELEMENTS_IN_VECTOR:usize;
  f_ZERO_pre:Prims.unit -> bool;
  f_ZERO_post:Prims.unit -> f_Vector -> bool;
  f_ZERO:x0: Prims.unit -> Prims.Pure f_Vector (f_ZERO_pre x0) (fun result -> f_ZERO_post x0 result);
  f_to_i32_array_pre:f_Vector -> bool;
  f_to_i32_array_post:f_Vector -> t_Array i32 (sz 8) -> bool;
  f_to_i32_array:x0: f_Vector
    -> Prims.Pure (t_Array i32 (sz 8))
        (f_to_i32_array_pre x0)
        (fun result -> f_to_i32_array_post x0 result);
  f_from_i32_array_pre:t_Array i32 (sz 8) -> bool;
  f_from_i32_array_post:t_Array i32 (sz 8) -> f_Vector -> bool;
  f_from_i32_array:x0: t_Array i32 (sz 8)
    -> Prims.Pure f_Vector (f_from_i32_array_pre x0) (fun result -> f_from_i32_array_post x0 result);
  f_add_constant_pre:f_Vector -> i32 -> bool;
  f_add_constant_post:f_Vector -> i32 -> f_Vector -> bool;
  f_add_constant:x0: f_Vector -> x1: i32
    -> Prims.Pure f_Vector
        (f_add_constant_pre x0 x1)
        (fun result -> f_add_constant_post x0 x1 result);
  f_add_pre:f_Vector -> f_Vector -> bool;
  f_add_post:f_Vector -> f_Vector -> f_Vector -> bool;
  f_add:x0: f_Vector -> x1: f_Vector
    -> Prims.Pure f_Vector (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result);
  f_sub_pre:f_Vector -> f_Vector -> bool;
  f_sub_post:f_Vector -> f_Vector -> f_Vector -> bool;
  f_sub:x0: f_Vector -> x1: f_Vector
    -> Prims.Pure f_Vector (f_sub_pre x0 x1) (fun result -> f_sub_post x0 x1 result);
  f_multiply_by_constant_pre:f_Vector -> i32 -> bool;
  f_multiply_by_constant_post:f_Vector -> i32 -> f_Vector -> bool;
  f_multiply_by_constant:x0: f_Vector -> x1: i32
    -> Prims.Pure f_Vector
        (f_multiply_by_constant_pre x0 x1)
        (fun result -> f_multiply_by_constant_post x0 x1 result);
  f_bitwise_and_with_constant_pre:f_Vector -> i32 -> bool;
  f_bitwise_and_with_constant_post:f_Vector -> i32 -> f_Vector -> bool;
  f_bitwise_and_with_constant:x0: f_Vector -> x1: i32
    -> Prims.Pure f_Vector
        (f_bitwise_and_with_constant_pre x0 x1)
        (fun result -> f_bitwise_and_with_constant_post x0 x1 result);
  f_shift_right_pre:f_Vector -> u8 -> bool;
  f_shift_right_post:f_Vector -> u8 -> f_Vector -> bool;
  f_shift_right:x0: f_Vector -> x1: u8
    -> Prims.Pure f_Vector (f_shift_right_pre x0 x1) (fun result -> f_shift_right_post x0 x1 result);
  f_shift_left_pre:f_Vector -> u8 -> bool;
  f_shift_left_post:f_Vector -> u8 -> f_Vector -> bool;
  f_shift_left:x0: f_Vector -> x1: u8
    -> Prims.Pure f_Vector (f_shift_left_pre x0 x1) (fun result -> f_shift_left_post x0 x1 result);
  f_modulo_a_constant_pre:f_Vector -> i32 -> bool;
  f_modulo_a_constant_post:f_Vector -> i32 -> f_Vector -> bool;
  f_modulo_a_constant:x0: f_Vector -> x1: i32
    -> Prims.Pure f_Vector
        (f_modulo_a_constant_pre x0 x1)
        (fun result -> f_modulo_a_constant_post x0 x1 result);
  f_barrett_reduce_pre:f_Vector -> bool;
  f_barrett_reduce_post:f_Vector -> f_Vector -> bool;
  f_barrett_reduce:x0: f_Vector
    -> Prims.Pure f_Vector (f_barrett_reduce_pre x0) (fun result -> f_barrett_reduce_post x0 result);
  f_montgomery_reduce_pre:f_Vector -> bool;
  f_montgomery_reduce_post:f_Vector -> f_Vector -> bool;
  f_montgomery_reduce:x0: f_Vector
    -> Prims.Pure f_Vector
        (f_montgomery_reduce_pre x0)
        (fun result -> f_montgomery_reduce_post x0 result);
  f_compress_1_pre:f_Vector -> bool;
  f_compress_1_post:f_Vector -> f_Vector -> bool;
  f_compress_1_:x0: f_Vector
    -> Prims.Pure f_Vector (f_compress_1__pre x0) (fun result -> f_compress_1__post x0 result);
  f_compress_pre:u8 -> f_Vector -> bool;
  f_compress_post:u8 -> f_Vector -> f_Vector -> bool;
  f_compress:x0: u8 -> x1: f_Vector
    -> Prims.Pure f_Vector (f_compress_pre x0 x1) (fun result -> f_compress_post x0 x1 result);
  f_ntt_layer_1_step_pre:f_Vector -> i32 -> i32 -> bool;
  f_ntt_layer_1_step_post:f_Vector -> i32 -> i32 -> f_Vector -> bool;
  f_ntt_layer_1_step:x0: f_Vector -> x1: i32 -> x2: i32
    -> Prims.Pure f_Vector
        (f_ntt_layer_1_step_pre x0 x1 x2)
        (fun result -> f_ntt_layer_1_step_post x0 x1 x2 result);
  f_ntt_layer_2_step_pre:f_Vector -> i32 -> bool;
  f_ntt_layer_2_step_post:f_Vector -> i32 -> f_Vector -> bool;
  f_ntt_layer_2_step:x0: f_Vector -> x1: i32
    -> Prims.Pure f_Vector
        (f_ntt_layer_2_step_pre x0 x1)
        (fun result -> f_ntt_layer_2_step_post x0 x1 result);
  f_inv_ntt_layer_1_step_pre:f_Vector -> i32 -> i32 -> bool;
  f_inv_ntt_layer_1_step_post:f_Vector -> i32 -> i32 -> f_Vector -> bool;
  f_inv_ntt_layer_1_step:x0: f_Vector -> x1: i32 -> x2: i32
    -> Prims.Pure f_Vector
        (f_inv_ntt_layer_1_step_pre x0 x1 x2)
        (fun result -> f_inv_ntt_layer_1_step_post x0 x1 x2 result);
  f_inv_ntt_layer_2_step_pre:f_Vector -> i32 -> bool;
  f_inv_ntt_layer_2_step_post:f_Vector -> i32 -> f_Vector -> bool;
  f_inv_ntt_layer_2_step:x0: f_Vector -> x1: i32
    -> Prims.Pure f_Vector
        (f_inv_ntt_layer_2_step_pre x0 x1)
        (fun result -> f_inv_ntt_layer_2_step_post x0 x1 result);
  f_ntt_multiply_pre:f_Vector -> f_Vector -> i32 -> i32 -> bool;
  f_ntt_multiply_post:f_Vector -> f_Vector -> i32 -> i32 -> f_Vector -> bool;
  f_ntt_multiply:x0: f_Vector -> x1: f_Vector -> x2: i32 -> x3: i32
    -> Prims.Pure f_Vector
        (f_ntt_multiply_pre x0 x1 x2 x3)
        (fun result -> f_ntt_multiply_post x0 x1 x2 x3 result);
  f_serialize_1_pre:f_Vector -> bool;
  f_serialize_1_post:f_Vector -> u8 -> bool;
  f_serialize_1_:x0: f_Vector
    -> Prims.Pure u8 (f_serialize_1__pre x0) (fun result -> f_serialize_1__post x0 result);
  f_deserialize_1_pre:u8 -> bool;
  f_deserialize_1_post:u8 -> f_Vector -> bool;
  f_deserialize_1_:x0: u8
    -> Prims.Pure f_Vector (f_deserialize_1__pre x0) (fun result -> f_deserialize_1__post x0 result);
  f_serialize_4_pre:f_Vector -> bool;
  f_serialize_4_post:f_Vector -> t_Array u8 (sz 4) -> bool;
  f_serialize_4_:x0: f_Vector
    -> Prims.Pure (t_Array u8 (sz 4))
        (f_serialize_4__pre x0)
        (fun result -> f_serialize_4__post x0 result);
  f_deserialize_4_pre:t_Slice u8 -> bool;
  f_deserialize_4_post:t_Slice u8 -> f_Vector -> bool;
  f_deserialize_4_:x0: t_Slice u8
    -> Prims.Pure f_Vector (f_deserialize_4__pre x0) (fun result -> f_deserialize_4__post x0 result);
  f_serialize_5_pre:f_Vector -> bool;
  f_serialize_5_post:f_Vector -> t_Array u8 (sz 5) -> bool;
  f_serialize_5_:x0: f_Vector
    -> Prims.Pure (t_Array u8 (sz 5))
        (f_serialize_5__pre x0)
        (fun result -> f_serialize_5__post x0 result);
  f_deserialize_5_pre:t_Slice u8 -> bool;
  f_deserialize_5_post:t_Slice u8 -> f_Vector -> bool;
  f_deserialize_5_:x0: t_Slice u8
    -> Prims.Pure f_Vector (f_deserialize_5__pre x0) (fun result -> f_deserialize_5__post x0 result);
  f_serialize_10_pre:f_Vector -> bool;
  f_serialize_10_post:f_Vector -> t_Array u8 (sz 10) -> bool;
  f_serialize_10_:x0: f_Vector
    -> Prims.Pure (t_Array u8 (sz 10))
        (f_serialize_10__pre x0)
        (fun result -> f_serialize_10__post x0 result);
  f_deserialize_10_pre:t_Slice u8 -> bool;
  f_deserialize_10_post:t_Slice u8 -> f_Vector -> bool;
  f_deserialize_10_:x0: t_Slice u8
    -> Prims.Pure f_Vector
        (f_deserialize_10__pre x0)
        (fun result -> f_deserialize_10__post x0 result);
  f_serialize_11_pre:f_Vector -> bool;
  f_serialize_11_post:f_Vector -> t_Array u8 (sz 11) -> bool;
  f_serialize_11_:x0: f_Vector
    -> Prims.Pure (t_Array u8 (sz 11))
        (f_serialize_11__pre x0)
        (fun result -> f_serialize_11__post x0 result);
  f_deserialize_11_pre:t_Slice u8 -> bool;
  f_deserialize_11_post:t_Slice u8 -> f_Vector -> bool;
  f_deserialize_11_:x0: t_Slice u8
    -> Prims.Pure f_Vector
        (f_deserialize_11__pre x0)
        (fun result -> f_deserialize_11__post x0 result);
  f_serialize_12_pre:f_Vector -> bool;
  f_serialize_12_post:f_Vector -> t_Array u8 (sz 12) -> bool;
  f_serialize_12_:x0: f_Vector
    -> Prims.Pure (t_Array u8 (sz 12))
        (f_serialize_12__pre x0)
        (fun result -> f_serialize_12__post x0 result);
  f_deserialize_12_pre:t_Slice u8 -> bool;
  f_deserialize_12_post:t_Slice u8 -> f_Vector -> bool;
  f_deserialize_12_:x0: t_Slice u8
    -> Prims.Pure f_Vector
        (f_deserialize_12__pre x0)
        (fun result -> f_deserialize_12__post x0 result);
  f_montgomery_multiply_fe_by_fer_pre:f_Vector -> i32 -> bool;
  f_montgomery_multiply_fe_by_fer_post:f_Vector -> i32 -> f_Vector -> bool;
  f_montgomery_multiply_fe_by_fer:x0: f_Vector -> x1: i32
    -> Prims.Pure f_Vector
        (f_montgomery_multiply_fe_by_fer_pre x0 x1)
        (fun result -> f_montgomery_multiply_fe_by_fer_post x0 x1 result);
  f_to_standard_domain_pre:f_Vector -> bool;
  f_to_standard_domain_post:f_Vector -> f_Vector -> bool;
  f_to_standard_domain:x0: f_Vector
    -> Prims.Pure f_Vector
        (f_to_standard_domain_pre x0)
        (fun result -> f_to_standard_domain_post x0 result);
  f_to_unsigned_representative_pre:f_Vector -> bool;
  f_to_unsigned_representative_post:f_Vector -> f_Vector -> bool;
  f_to_unsigned_representative:x0: f_Vector
    -> Prims.Pure f_Vector
        (f_to_unsigned_representative_pre x0)
        (fun result -> f_to_unsigned_representative_post x0 result);
  f_decompress_1_pre:f_Vector -> bool;
  f_decompress_1_post:f_Vector -> f_Vector -> bool;
  f_decompress_1_:x0: f_Vector
    -> Prims.Pure f_Vector (f_decompress_1__pre x0) (fun result -> f_decompress_1__post x0 result);
  f_decompress_pre:u8 -> f_Vector -> bool;
  f_decompress_post:u8 -> f_Vector -> f_Vector -> bool;
  f_decompress:x0: u8 -> x1: f_Vector
    -> Prims.Pure f_Vector (f_decompress_pre x0 x1) (fun result -> f_decompress_post x0 x1 result)
}
