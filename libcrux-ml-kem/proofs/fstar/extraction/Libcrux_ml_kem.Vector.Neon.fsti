module Libcrux_ml_kem.Vector.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Neon.Vector_type in
  ()

val rej_sample (a: t_Slice u8) (result: t_Slice i16)
    : Prims.Pure (t_Slice i16 & usize) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_kem.Vector.Traits.t_Operations
Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post
    =
    (fun (_: Prims.unit) (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_ZERO = (fun (_: Prims.unit) -> Libcrux_ml_kem.Vector.Neon.Vector_type.v_ZERO ());
    f_from_i16_array_pre = (fun (array: t_Slice i16) -> true);
    f_from_i16_array_post
    =
    (fun (array: t_Slice i16) (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_from_i16_array
    =
    (fun (array: t_Slice i16) -> Libcrux_ml_kem.Vector.Neon.Vector_type.from_i16_array array);
    f_to_i16_array_pre = (fun (x: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_to_i16_array_post
    =
    (fun (x: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (out: t_Array i16 (sz 16)) ->
        true);
    f_to_i16_array
    =
    (fun (x: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Vector_type.to_i16_array x);
    f_add_pre
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_add_post
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_add
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        Libcrux_ml_kem.Vector.Neon.Arithmetic.add lhs rhs);
    f_sub_pre
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_sub_post
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_sub
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        Libcrux_ml_kem.Vector.Neon.Arithmetic.sub lhs rhs);
    f_multiply_by_constant_pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (c: i16) -> true);
    f_multiply_by_constant_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (c: i16)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_multiply_by_constant
    =
    (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (c: i16) ->
        Libcrux_ml_kem.Vector.Neon.Arithmetic.multiply_by_constant v c);
    f_bitwise_and_with_constant_pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (c: i16) -> true);
    f_bitwise_and_with_constant_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (c: i16)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_bitwise_and_with_constant
    =
    (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (c: i16) ->
        Libcrux_ml_kem.Vector.Neon.Arithmetic.bitwise_and_with_constant v c);
    f_shift_right_pre
    =
    (fun (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_shift_right_post
    =
    (fun
        (v_SHIFT_BY: i32)
        (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_shift_right
    =
    (fun (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Arithmetic.shift_right v_SHIFT_BY v);
    f_cond_subtract_3329_pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_cond_subtract_3329_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_cond_subtract_3329_
    =
    (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Arithmetic.cond_subtract_3329_ v);
    f_barrett_reduce_pre = (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_barrett_reduce_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_barrett_reduce
    =
    (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Arithmetic.barrett_reduce v);
    f_montgomery_multiply_by_constant_pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (c: i16) -> true);
    f_montgomery_multiply_by_constant_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (c: i16)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_montgomery_multiply_by_constant
    =
    (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (c: i16) ->
        Libcrux_ml_kem.Vector.Neon.Arithmetic.montgomery_multiply_by_constant v c);
    f_compress_1_pre = (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_compress_1_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_compress_1_
    =
    (fun (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Compress.compress_1_ v);
    f_compress_pre
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        true);
    f_compress_post
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_compress
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Compress.compress v_COEFFICIENT_BITS v);
    f_decompress_ciphertext_coefficient_pre
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        true);
    f_decompress_ciphertext_coefficient_post
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_decompress_ciphertext_coefficient
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Compress.decompress_ciphertext_coefficient v_COEFFICIENT_BITS v);
    f_ntt_layer_1_step_pre
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        true);
    f_ntt_layer_1_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_ntt_layer_1_step
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        Libcrux_ml_kem.Vector.Neon.Ntt.ntt_layer_1_step a zeta1 zeta2 zeta3 zeta4);
    f_ntt_layer_2_step_pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta1: i16) (zeta2: i16) ->
        true);
    f_ntt_layer_2_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_ntt_layer_2_step
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta1: i16) (zeta2: i16) ->
        Libcrux_ml_kem.Vector.Neon.Ntt.ntt_layer_2_step a zeta1 zeta2);
    f_ntt_layer_3_step_pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta: i16) -> true);
    f_ntt_layer_3_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta: i16)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_ntt_layer_3_step
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta: i16) ->
        Libcrux_ml_kem.Vector.Neon.Ntt.ntt_layer_3_step a zeta);
    f_inv_ntt_layer_1_step_pre
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        true);
    f_inv_ntt_layer_1_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_inv_ntt_layer_1_step
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        Libcrux_ml_kem.Vector.Neon.Ntt.inv_ntt_layer_1_step a zeta1 zeta2 zeta3 zeta4);
    f_inv_ntt_layer_2_step_pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta1: i16) (zeta2: i16) ->
        true);
    f_inv_ntt_layer_2_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_inv_ntt_layer_2_step
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta1: i16) (zeta2: i16) ->
        Libcrux_ml_kem.Vector.Neon.Ntt.inv_ntt_layer_2_step a zeta1 zeta2);
    f_inv_ntt_layer_3_step_pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta: i16) -> true);
    f_inv_ntt_layer_3_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta: i16)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_inv_ntt_layer_3_step
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta: i16) ->
        Libcrux_ml_kem.Vector.Neon.Ntt.inv_ntt_layer_3_step a zeta);
    f_ntt_multiply_pre
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        true);
    f_ntt_multiply_post
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        ->
        true);
    f_ntt_multiply
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        Libcrux_ml_kem.Vector.Neon.Ntt.ntt_multiply lhs rhs zeta1 zeta2 zeta3 zeta4);
    f_serialize_1_pre = (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_serialize_1_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (out: t_Array u8 (sz 2)) ->
        true);
    f_serialize_1_
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Serialize.serialize_1_ a);
    f_deserialize_1_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_1_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_deserialize_1_
    =
    (fun (a: t_Slice u8) -> Libcrux_ml_kem.Vector.Neon.Serialize.deserialize_1_ a);
    f_serialize_4_pre = (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_serialize_4_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (out: t_Array u8 (sz 8)) ->
        true);
    f_serialize_4_
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Serialize.serialize_4_ a);
    f_deserialize_4_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_4_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_deserialize_4_
    =
    (fun (a: t_Slice u8) -> Libcrux_ml_kem.Vector.Neon.Serialize.deserialize_4_ a);
    f_serialize_5_pre = (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_serialize_5_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (out: t_Array u8 (sz 10)) ->
        true);
    f_serialize_5_
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Serialize.serialize_5_ a);
    f_deserialize_5_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_5_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_deserialize_5_
    =
    (fun (a: t_Slice u8) -> Libcrux_ml_kem.Vector.Neon.Serialize.deserialize_5_ a);
    f_serialize_10_pre = (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_serialize_10_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (out: t_Array u8 (sz 20)) ->
        true);
    f_serialize_10_
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Serialize.serialize_10_ a);
    f_deserialize_10_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_10_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_deserialize_10_
    =
    (fun (a: t_Slice u8) -> Libcrux_ml_kem.Vector.Neon.Serialize.deserialize_10_ a);
    f_serialize_11_pre = (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_serialize_11_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (out: t_Array u8 (sz 22)) ->
        true);
    f_serialize_11_
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Serialize.serialize_11_ a);
    f_deserialize_11_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_11_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_deserialize_11_
    =
    (fun (a: t_Slice u8) -> Libcrux_ml_kem.Vector.Neon.Serialize.deserialize_11_ a);
    f_serialize_12_pre = (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_serialize_12_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (out: t_Array u8 (sz 24)) ->
        true);
    f_serialize_12_
    =
    (fun (a: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) ->
        Libcrux_ml_kem.Vector.Neon.Serialize.serialize_12_ a);
    f_deserialize_12_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_12_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) -> true);
    f_deserialize_12_
    =
    (fun (a: t_Slice u8) -> Libcrux_ml_kem.Vector.Neon.Serialize.deserialize_12_ a);
    f_rej_sample_pre = (fun (a: t_Slice u8) (out: t_Slice i16) -> true);
    f_rej_sample_post
    =
    (fun (a: t_Slice u8) (out: t_Slice i16) (out2: (t_Slice i16 & usize)) -> true);
    f_rej_sample
    =
    fun (a: t_Slice u8) (out: t_Slice i16) ->
      let tmp0, out1:(t_Slice i16 & usize) = rej_sample a out in
      let out:t_Slice i16 = tmp0 in
      let hax_temp_output:usize = out1 in
      out, hax_temp_output <: (t_Slice i16 & usize)
  }
