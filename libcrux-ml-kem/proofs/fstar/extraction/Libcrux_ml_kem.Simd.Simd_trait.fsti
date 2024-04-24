module Libcrux_ml_kem.Simd.Simd_trait
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Operations (v_Self: Type) = {
  f_Vector:Type;
  f_Vector_8701872305793597044:Core.Clone.t_Clone f_Vector;
  f_Vector_15713626723705489010:Core.Marker.t_Copy f_Vector;
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
    -> Prims.Pure f_Vector (f_compress_1_pre x0) (fun result -> f_compress_1_post x0 result);
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
    -> Prims.Pure u8 (f_serialize_1_pre x0) (fun result -> f_serialize_1_post x0 result);
  f_deserialize_1_pre:u8 -> bool;
  f_deserialize_1_post:u8 -> f_Vector -> bool;
  f_deserialize_1_:x0: u8
    -> Prims.Pure f_Vector (f_deserialize_1_pre x0) (fun result -> f_deserialize_1_post x0 result);
  f_serialize_4_pre:f_Vector -> bool;
  f_serialize_4_post:f_Vector -> t_Array u8 (sz 4) -> bool;
  f_serialize_4_:x0: f_Vector
    -> Prims.Pure (t_Array u8 (sz 4))
        (f_serialize_4_pre x0)
        (fun result -> f_serialize_4_post x0 result);
  f_deserialize_4_pre:t_Slice u8 -> bool;
  f_deserialize_4_post:t_Slice u8 -> f_Vector -> bool;
  f_deserialize_4_:x0: t_Slice u8
    -> Prims.Pure f_Vector (f_deserialize_4_pre x0) (fun result -> f_deserialize_4_post x0 result);
  f_serialize_5_pre:f_Vector -> bool;
  f_serialize_5_post:f_Vector -> t_Array u8 (sz 5) -> bool;
  f_serialize_5_:x0: f_Vector
    -> Prims.Pure (t_Array u8 (sz 5))
        (f_serialize_5_pre x0)
        (fun result -> f_serialize_5_post x0 result);
  f_deserialize_5_pre:t_Slice u8 -> bool;
  f_deserialize_5_post:t_Slice u8 -> f_Vector -> bool;
  f_deserialize_5_:x0: t_Slice u8
    -> Prims.Pure f_Vector (f_deserialize_5_pre x0) (fun result -> f_deserialize_5_post x0 result);
  f_serialize_10_pre:f_Vector -> bool;
  f_serialize_10_post:f_Vector -> t_Array u8 (sz 10) -> bool;
  f_serialize_10_:x0: f_Vector
    -> Prims.Pure (t_Array u8 (sz 10))
        (f_serialize_10_pre x0)
        (fun result -> f_serialize_10_post x0 result);
  f_deserialize_10_pre:t_Slice u8 -> bool;
  f_deserialize_10_post:t_Slice u8 -> f_Vector -> bool;
  f_deserialize_10_:x0: t_Slice u8
    -> Prims.Pure f_Vector (f_deserialize_10_pre x0) (fun result -> f_deserialize_10_post x0 result);
  f_serialize_11_pre:f_Vector -> bool;
  f_serialize_11_post:f_Vector -> t_Array u8 (sz 11) -> bool;
  f_serialize_11_:x0: f_Vector
    -> Prims.Pure (t_Array u8 (sz 11))
        (f_serialize_11_pre x0)
        (fun result -> f_serialize_11_post x0 result);
  f_deserialize_11_pre:t_Slice u8 -> bool;
  f_deserialize_11_post:t_Slice u8 -> f_Vector -> bool;
  f_deserialize_11_:x0: t_Slice u8
    -> Prims.Pure f_Vector (f_deserialize_11_pre x0) (fun result -> f_deserialize_11_post x0 result);
  f_serialize_12_pre:f_Vector -> bool;
  f_serialize_12_post:f_Vector -> t_Array u8 (sz 12) -> bool;
  f_serialize_12_:x0: f_Vector
    -> Prims.Pure (t_Array u8 (sz 12))
        (f_serialize_12_pre x0)
        (fun result -> f_serialize_12_post x0 result);
  f_deserialize_12_pre:t_Slice u8 -> bool;
  f_deserialize_12_post:t_Slice u8 -> f_Vector -> bool;
  f_deserialize_12_:x0: t_Slice u8
    -> Prims.Pure f_Vector (f_deserialize_12_pre x0) (fun result -> f_deserialize_12_post x0 result)
}

class t_GenericOperations (v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]v_15630088582682752894:t_Operations v_Self;
  f_montgomery_multiply_fe_by_fer_pre:v_15630088582682752894.f_Vector -> i32 -> bool;
  f_montgomery_multiply_fe_by_fer_post:
      v_15630088582682752894.f_Vector ->
      i32 ->
      v_15630088582682752894.f_Vector
    -> bool;
  f_montgomery_multiply_fe_by_fer:x0: v_15630088582682752894.f_Vector -> x1: i32
    -> Prims.Pure v_15630088582682752894.f_Vector
        (f_montgomery_multiply_fe_by_fer_pre x0 x1)
        (fun result -> f_montgomery_multiply_fe_by_fer_post x0 x1 result);
  f_to_standard_domain_pre:v_15630088582682752894.f_Vector -> bool;
  f_to_standard_domain_post:v_15630088582682752894.f_Vector -> v_15630088582682752894.f_Vector
    -> bool;
  f_to_standard_domain:x0: v_15630088582682752894.f_Vector
    -> Prims.Pure v_15630088582682752894.f_Vector
        (f_to_standard_domain_pre x0)
        (fun result -> f_to_standard_domain_post x0 result);
  f_to_unsigned_representative_pre:v_15630088582682752894.f_Vector -> bool;
  f_to_unsigned_representative_post:
      v_15630088582682752894.f_Vector ->
      v_15630088582682752894.f_Vector
    -> bool;
  f_to_unsigned_representative:x0: v_15630088582682752894.f_Vector
    -> Prims.Pure v_15630088582682752894.f_Vector
        (f_to_unsigned_representative_pre x0)
        (fun result -> f_to_unsigned_representative_post x0 result);
  f_decompress_1_pre:v_15630088582682752894.f_Vector -> bool;
  f_decompress_1_post:v_15630088582682752894.f_Vector -> v_15630088582682752894.f_Vector -> bool;
  f_decompress_1_:x0: v_15630088582682752894.f_Vector
    -> Prims.Pure v_15630088582682752894.f_Vector
        (f_decompress_1_pre x0)
        (fun result -> f_decompress_1_post x0 result);
  f_decompress_pre:u8 -> v_15630088582682752894.f_Vector -> bool;
  f_decompress_post:u8 -> v_15630088582682752894.f_Vector -> v_15630088582682752894.f_Vector -> bool;
  f_decompress:x0: u8 -> x1: v_15630088582682752894.f_Vector
    -> Prims.Pure v_15630088582682752894.f_Vector
        (f_decompress_pre x0 x1)
        (fun result -> f_decompress_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_T)
    : t_GenericOperations v_T =
  {
    v_15630088582682752894 = i1;
    f_montgomery_multiply_fe_by_fer_pre = (fun (v: i1.f_Vector) (fer: i32) -> true);
    f_montgomery_multiply_fe_by_fer_post
    =
    (fun (v: i1.f_Vector) (fer: i32) (out: i1.f_Vector) -> true);
    f_montgomery_multiply_fe_by_fer
    =
    (fun (v: i1.f_Vector) (fer: i32) ->
        let t = f_multiply_by_constant v fer in
        f_montgomery_reduce t);
    f_to_standard_domain_pre = (fun (v: i1.f_Vector) -> true);
    f_to_standard_domain_post = (fun (v: i1.f_Vector) (out: i1.f_Vector) -> true);
    f_to_standard_domain
    =
    (fun (v: i1.f_Vector) ->
        let t =
          f_multiply_by_constant v
            Libcrux_ml_kem.Arithmetic.v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS
        in
        f_montgomery_reduce t);
    f_to_unsigned_representative_pre = (fun (a: i1.f_Vector) -> true);
    f_to_unsigned_representative_post = (fun (a: i1.f_Vector) (out: i1.f_Vector) -> true);
    f_to_unsigned_representative
    =
    (fun (a: i1.f_Vector) ->
        let t = f_shift_right a 31uy in
        let fm = f_bitwise_and_with_constant t Libcrux_ml_kem.Constants.v_FIELD_MODULUS in
        f_add a fm);
    f_decompress_1_pre = (fun (v: i1.f_Vector) -> true);
    f_decompress_1_post = (fun (v: i1.f_Vector) (out: i1.f_Vector) -> true);
    f_decompress_1_
    =
    (fun (v: i1.f_Vector) ->
        f_bitwise_and_with_constant (f_sub (f_ZERO () <: i1.f_Vector) v <: i1.f_Vector) 1665l);
    f_decompress_pre = (fun (coefficient_bits: u8) (v: i1.f_Vector) -> true);
    f_decompress_post = (fun (coefficient_bits: u8) (v: i1.f_Vector) (out: i1.f_Vector) -> true);
    f_decompress
    =
    fun (coefficient_bits: u8) (v: i1.f_Vector) ->
      let decompressed = f_multiply_by_constant v Libcrux_ml_kem.Constants.v_FIELD_MODULUS in
      let decompressed =
        f_add_constant (f_shift_left decompressed 1uy <: i1.f_Vector)
          (1l <<! coefficient_bits <: i32)
      in
      let decompressed = f_shift_right decompressed (coefficient_bits +! 1uy <: u8) in
      decompressed
  }
