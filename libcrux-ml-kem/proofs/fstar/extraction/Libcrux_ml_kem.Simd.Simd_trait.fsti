module Libcrux_ml_kem.Simd.Simd_trait
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_GenericOperations (v_Self: Type) = {
  f_montgomery_multiply_fe_by_fer_pre:v_Self -> i32 -> bool;
  f_montgomery_multiply_fe_by_fer_post:v_Self -> i32 -> v_Self -> bool;
  f_montgomery_multiply_fe_by_fer:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self
        (f_montgomery_multiply_fe_by_fer_pre x0 x1)
        (fun result -> f_montgomery_multiply_fe_by_fer_post x0 x1 result);
  f_to_standard_domain_pre:v_Self -> bool;
  f_to_standard_domain_post:v_Self -> v_Self -> bool;
  f_to_standard_domain:x0: v_Self
    -> Prims.Pure v_Self
        (f_to_standard_domain_pre x0)
        (fun result -> f_to_standard_domain_post x0 result);
  f_to_unsigned_representative_pre:v_Self -> bool;
  f_to_unsigned_representative_post:v_Self -> v_Self -> bool;
  f_to_unsigned_representative:x0: v_Self
    -> Prims.Pure v_Self
        (f_to_unsigned_representative_pre x0)
        (fun result -> f_to_unsigned_representative_post x0 result);
  f_decompress_1_pre:v_Self -> bool;
  f_decompress_1_post:v_Self -> v_Self -> bool;
  f_decompress_1_:x0: v_Self
    -> Prims.Pure v_Self (f_decompress_1__pre x0) (fun result -> f_decompress_1__post x0 result);
  f_decompress_pre:v_COEFFICIENT_BITS: i32 -> v_Self -> bool;
  f_decompress_post:v_COEFFICIENT_BITS: i32 -> v_Self -> v_Self -> bool;
  f_decompress:v_COEFFICIENT_BITS: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_decompress_pre v_COEFFICIENT_BITS x0)
        (fun result -> f_decompress_post v_COEFFICIENT_BITS x0 result)
}

class t_Operations (v_Self: Type) = {
  f_ZERO_pre:Prims.unit -> bool;
  f_ZERO_post:Prims.unit -> v_Self -> bool;
  f_ZERO:x0: Prims.unit -> Prims.Pure v_Self (f_ZERO_pre x0) (fun result -> f_ZERO_post x0 result);
  f_to_i32_array_pre:v_Self -> bool;
  f_to_i32_array_post:v_Self -> t_Array i32 (sz 8) -> bool;
  f_to_i32_array:x0: v_Self
    -> Prims.Pure (t_Array i32 (sz 8))
        (f_to_i32_array_pre x0)
        (fun result -> f_to_i32_array_post x0 result);
  f_from_i32_array_pre:t_Array i32 (sz 8) -> bool;
  f_from_i32_array_post:t_Array i32 (sz 8) -> v_Self -> bool;
  f_from_i32_array:x0: t_Array i32 (sz 8)
    -> Prims.Pure v_Self (f_from_i32_array_pre x0) (fun result -> f_from_i32_array_post x0 result);
  f_add_constant_pre:v_Self -> i32 -> bool;
  f_add_constant_post:v_Self -> i32 -> v_Self -> bool;
  f_add_constant:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self (f_add_constant_pre x0 x1) (fun result -> f_add_constant_post x0 x1 result);
  f_add_pre:v_Self -> v_Self -> bool;
  f_add_post:v_Self -> v_Self -> v_Self -> bool;
  f_add:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result);
  f_sub_pre:v_Self -> v_Self -> bool;
  f_sub_post:v_Self -> v_Self -> v_Self -> bool;
  f_sub:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_sub_pre x0 x1) (fun result -> f_sub_post x0 x1 result);
  f_multiply_by_constant_pre:v_Self -> i32 -> bool;
  f_multiply_by_constant_post:v_Self -> i32 -> v_Self -> bool;
  f_multiply_by_constant:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self
        (f_multiply_by_constant_pre x0 x1)
        (fun result -> f_multiply_by_constant_post x0 x1 result);
  f_bitwise_and_with_constant_pre:v_Self -> i32 -> bool;
  f_bitwise_and_with_constant_post:v_Self -> i32 -> v_Self -> bool;
  f_bitwise_and_with_constant:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self
        (f_bitwise_and_with_constant_pre x0 x1)
        (fun result -> f_bitwise_and_with_constant_post x0 x1 result);
  f_shift_right_pre:v_SHIFT_BY: i32 -> v_Self -> bool;
  f_shift_right_post:v_SHIFT_BY: i32 -> v_Self -> v_Self -> bool;
  f_shift_right:v_SHIFT_BY: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_shift_right_pre v_SHIFT_BY x0)
        (fun result -> f_shift_right_post v_SHIFT_BY x0 result);
  f_shift_left_pre:v_SHIFT_BY: i32 -> v_Self -> bool;
  f_shift_left_post:v_SHIFT_BY: i32 -> v_Self -> v_Self -> bool;
  f_shift_left:v_SHIFT_BY: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_shift_left_pre v_SHIFT_BY x0)
        (fun result -> f_shift_left_post v_SHIFT_BY x0 result);
  f_cond_subtract_3329_pre:v_Self -> bool;
  f_cond_subtract_3329_post:v_Self -> v_Self -> bool;
  f_cond_subtract_3329_:x0: v_Self
    -> Prims.Pure v_Self
        (f_cond_subtract_3329__pre x0)
        (fun result -> f_cond_subtract_3329__post x0 result);
  f_barrett_reduce_pre:v_Self -> bool;
  f_barrett_reduce_post:v_Self -> v_Self -> bool;
  f_barrett_reduce:x0: v_Self
    -> Prims.Pure v_Self (f_barrett_reduce_pre x0) (fun result -> f_barrett_reduce_post x0 result);
  f_montgomery_reduce_pre:v_Self -> bool;
  f_montgomery_reduce_post:v_Self -> v_Self -> bool;
  f_montgomery_reduce:x0: v_Self
    -> Prims.Pure v_Self
        (f_montgomery_reduce_pre x0)
        (fun result -> f_montgomery_reduce_post x0 result);
  f_compress_1_pre:v_Self -> bool;
  f_compress_1_post:v_Self -> v_Self -> bool;
  f_compress_1_:x0: v_Self
    -> Prims.Pure v_Self (f_compress_1__pre x0) (fun result -> f_compress_1__post x0 result);
  f_compress_pre:u8 -> v_Self -> bool;
  f_compress_post:u8 -> v_Self -> v_Self -> bool;
  f_compress:x0: u8 -> x1: v_Self
    -> Prims.Pure v_Self (f_compress_pre x0 x1) (fun result -> f_compress_post x0 x1 result);
  f_ntt_layer_1_step_pre:v_Self -> i32 -> i32 -> bool;
  f_ntt_layer_1_step_post:v_Self -> i32 -> i32 -> v_Self -> bool;
  f_ntt_layer_1_step:x0: v_Self -> x1: i32 -> x2: i32
    -> Prims.Pure v_Self
        (f_ntt_layer_1_step_pre x0 x1 x2)
        (fun result -> f_ntt_layer_1_step_post x0 x1 x2 result);
  f_ntt_layer_2_step_pre:v_Self -> i32 -> bool;
  f_ntt_layer_2_step_post:v_Self -> i32 -> v_Self -> bool;
  f_ntt_layer_2_step:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self
        (f_ntt_layer_2_step_pre x0 x1)
        (fun result -> f_ntt_layer_2_step_post x0 x1 result);
  f_inv_ntt_layer_1_step_pre:v_Self -> i32 -> i32 -> bool;
  f_inv_ntt_layer_1_step_post:v_Self -> i32 -> i32 -> v_Self -> bool;
  f_inv_ntt_layer_1_step:x0: v_Self -> x1: i32 -> x2: i32
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_1_step_pre x0 x1 x2)
        (fun result -> f_inv_ntt_layer_1_step_post x0 x1 x2 result);
  f_inv_ntt_layer_2_step_pre:v_Self -> i32 -> bool;
  f_inv_ntt_layer_2_step_post:v_Self -> i32 -> v_Self -> bool;
  f_inv_ntt_layer_2_step:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_2_step_pre x0 x1)
        (fun result -> f_inv_ntt_layer_2_step_post x0 x1 result);
  f_ntt_multiply_pre:v_Self -> v_Self -> i32 -> i32 -> bool;
  f_ntt_multiply_post:v_Self -> v_Self -> i32 -> i32 -> v_Self -> bool;
  f_ntt_multiply:x0: v_Self -> x1: v_Self -> x2: i32 -> x3: i32
    -> Prims.Pure v_Self
        (f_ntt_multiply_pre x0 x1 x2 x3)
        (fun result -> f_ntt_multiply_post x0 x1 x2 x3 result);
  f_serialize_1_pre:v_Self -> bool;
  f_serialize_1_post:v_Self -> u8 -> bool;
  f_serialize_1_:x0: v_Self
    -> Prims.Pure u8 (f_serialize_1__pre x0) (fun result -> f_serialize_1__post x0 result);
  f_deserialize_1_pre:u8 -> bool;
  f_deserialize_1_post:u8 -> v_Self -> bool;
  f_deserialize_1_:x0: u8
    -> Prims.Pure v_Self (f_deserialize_1__pre x0) (fun result -> f_deserialize_1__post x0 result);
  f_serialize_4_pre:v_Self -> bool;
  f_serialize_4_post:v_Self -> t_Array u8 (sz 4) -> bool;
  f_serialize_4_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 4))
        (f_serialize_4__pre x0)
        (fun result -> f_serialize_4__post x0 result);
  f_deserialize_4_pre:t_Slice u8 -> bool;
  f_deserialize_4_post:t_Slice u8 -> v_Self -> bool;
  f_deserialize_4_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_4__pre x0) (fun result -> f_deserialize_4__post x0 result);
  f_serialize_5_pre:v_Self -> bool;
  f_serialize_5_post:v_Self -> t_Array u8 (sz 5) -> bool;
  f_serialize_5_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 5))
        (f_serialize_5__pre x0)
        (fun result -> f_serialize_5__post x0 result);
  f_deserialize_5_pre:t_Slice u8 -> bool;
  f_deserialize_5_post:t_Slice u8 -> v_Self -> bool;
  f_deserialize_5_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_5__pre x0) (fun result -> f_deserialize_5__post x0 result);
  f_serialize_10_pre:v_Self -> bool;
  f_serialize_10_post:v_Self -> t_Array u8 (sz 10) -> bool;
  f_serialize_10_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 10))
        (f_serialize_10__pre x0)
        (fun result -> f_serialize_10__post x0 result);
  f_deserialize_10_pre:t_Slice u8 -> bool;
  f_deserialize_10_post:t_Slice u8 -> v_Self -> bool;
  f_deserialize_10_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_10__pre x0) (fun result -> f_deserialize_10__post x0 result);
  f_serialize_11_pre:v_Self -> bool;
  f_serialize_11_post:v_Self -> t_Array u8 (sz 11) -> bool;
  f_serialize_11_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 11))
        (f_serialize_11__pre x0)
        (fun result -> f_serialize_11__post x0 result);
  f_deserialize_11_pre:t_Slice u8 -> bool;
  f_deserialize_11_post:t_Slice u8 -> v_Self -> bool;
  f_deserialize_11_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_11__pre x0) (fun result -> f_deserialize_11__post x0 result);
  f_serialize_12_pre:v_Self -> bool;
  f_serialize_12_post:v_Self -> t_Array u8 (sz 12) -> bool;
  f_serialize_12_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 12))
        (f_serialize_12__pre x0)
        (fun result -> f_serialize_12__post x0 result);
  f_deserialize_12_pre:t_Slice u8 -> bool;
  f_deserialize_12_post:t_Slice u8 -> v_Self -> bool;
  f_deserialize_12_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_12__pre x0) (fun result -> f_deserialize_12__post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core.Marker.t_Copy v_T)
    : t_GenericOperations v_T =
  {
    f_montgomery_multiply_fe_by_fer_pre = (fun (v: v_T) (fer: i32) -> true);
    f_montgomery_multiply_fe_by_fer_post = (fun (v: v_T) (fer: i32) (out: v_T) -> true);
    f_montgomery_multiply_fe_by_fer
    =
    (fun (v: v_T) (fer: i32) ->
        let t:v_T = f_multiply_by_constant v fer in
        f_montgomery_reduce t);
    f_to_standard_domain_pre = (fun (v: v_T) -> true);
    f_to_standard_domain_post = (fun (v: v_T) (out: v_T) -> true);
    f_to_standard_domain
    =
    (fun (v: v_T) ->
        let t:v_T =
          f_multiply_by_constant v
            Libcrux_ml_kem.Arithmetic.v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS
        in
        f_montgomery_reduce t);
    f_to_unsigned_representative_pre = (fun (a: v_T) -> true);
    f_to_unsigned_representative_post = (fun (a: v_T) (out: v_T) -> true);
    f_to_unsigned_representative
    =
    (fun (a: v_T) ->
        let t:v_T = f_shift_right 31l a in
        let fm:v_T = f_bitwise_and_with_constant t Libcrux_ml_kem.Constants.v_FIELD_MODULUS in
        f_add a fm);
    f_decompress_1_pre = (fun (v: v_T) -> true);
    f_decompress_1_post = (fun (v: v_T) (out: v_T) -> true);
    f_decompress_1_
    =
    (fun (v: v_T) -> f_bitwise_and_with_constant (f_sub (f_ZERO () <: v_T) v <: v_T) 1665l);
    f_decompress_pre = (fun (v_COEFFICIENT_BITS: i32) (v: v_T) -> true);
    f_decompress_post = (fun (v_COEFFICIENT_BITS: i32) (v: v_T) (out: v_T) -> true);
    f_decompress
    =
    fun (v_COEFFICIENT_BITS: i32) (v: v_T) ->
      let decompressed:v_T = f_multiply_by_constant v Libcrux_ml_kem.Constants.v_FIELD_MODULUS in
      let decompressed:v_T =
        f_add_constant (f_shift_left 1l decompressed <: v_T) (1l <<! v_COEFFICIENT_BITS <: i32)
      in
      let decompressed_1_:v_T = f_shift_right v_COEFFICIENT_BITS decompressed in
      f_shift_right 1l decompressed_1_
  }

let v_FIELD_ELEMENTS_IN_VECTOR: usize = sz 8
