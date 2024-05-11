module Libcrux_polynomials_aarch64
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_traits.t_Operations Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector =
  {
    _super_957087622381469234 = FStar.Tactics.Typeclasses.solve;
    _super_2101570567305961368 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post
    =
    (fun (_: Prims.unit) (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_ZERO = (fun (_: Prims.unit) -> Libcrux_polynomials_aarch64.Simd128ops.v_ZERO ());
    f_to_i16_array_pre = (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_to_i16_array_post
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (out: t_Array i16 (sz 16)) ->
        true);
    f_to_i16_array
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.to_i16_array v);
    f_from_i16_array_pre = (fun (array: t_Array i16 (sz 16)) -> true);
    f_from_i16_array_post
    =
    (fun
        (array: t_Array i16 (sz 16))
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_from_i16_array
    =
    (fun (array: t_Array i16 (sz 16)) -> Libcrux_polynomials_aarch64.Simd128ops.from_i16_array array
    );
    f_add_pre
    =
    (fun
        (lhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (rhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_add_post
    =
    (fun
        (lhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (rhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_add
    =
    (fun
        (lhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (rhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        Libcrux_polynomials_aarch64.Simd128ops.add lhs rhs);
    f_sub_pre
    =
    (fun
        (lhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (rhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_sub_post
    =
    (fun
        (lhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (rhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_sub
    =
    (fun
        (lhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (rhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        Libcrux_polynomials_aarch64.Simd128ops.sub lhs rhs);
    f_multiply_by_constant_pre
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (c: i16) -> true);
    f_multiply_by_constant_post
    =
    (fun
        (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (c: i16)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_multiply_by_constant
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (c: i16) ->
        Libcrux_polynomials_aarch64.Simd128ops.multiply_by_constant v c);
    f_bitwise_and_with_constant_pre
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (c: i16) -> true);
    f_bitwise_and_with_constant_post
    =
    (fun
        (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (c: i16)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_bitwise_and_with_constant
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (c: i16) ->
        Libcrux_polynomials_aarch64.Simd128ops.bitwise_and_with_constant v c);
    f_shift_right_pre
    =
    (fun (v_SHIFT_BY: i32) (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_shift_right_post
    =
    (fun
        (v_SHIFT_BY: i32)
        (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_shift_right
    =
    (fun (v_SHIFT_BY: i32) (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.shift_right v_SHIFT_BY v);
    f_shift_left_pre
    =
    (fun (v_SHIFT_BY: i32) (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_shift_left_post
    =
    (fun
        (v_SHIFT_BY: i32)
        (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_shift_left
    =
    (fun (v_SHIFT_BY: i32) (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.shift_left v_SHIFT_BY v);
    f_cond_subtract_3329_pre
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_cond_subtract_3329_post
    =
    (fun
        (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_cond_subtract_3329_
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.cond_subtract_3329_ v);
    f_barrett_reduce_pre = (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_barrett_reduce_post
    =
    (fun
        (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_barrett_reduce
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.barrett_reduce v);
    f_montgomery_multiply_by_constant_pre
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (c: i16) -> true);
    f_montgomery_multiply_by_constant_post
    =
    (fun
        (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (c: i16)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_montgomery_multiply_by_constant
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (c: i16) ->
        Libcrux_polynomials_aarch64.Simd128ops.montgomery_multiply_by_constant v c);
    f_compress_1_pre = (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_compress_1_post
    =
    (fun
        (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_compress_1_
    =
    (fun (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.compress_1_ v);
    f_compress_pre
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        true);
    f_compress_post
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_compress
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.compress v_COEFFICIENT_BITS v);
    f_decompress_pre
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        true);
    f_decompress_post
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_decompress
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.decompress v_COEFFICIENT_BITS v);
    f_ntt_layer_1_step_pre
    =
    (fun
        (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        true);
    f_ntt_layer_1_step_post
    =
    (fun
        (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_ntt_layer_1_step
    =
    (fun
        (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        Libcrux_polynomials_aarch64.Simd128ops.ntt_layer_1_step a zeta1 zeta2 zeta3 zeta4);
    f_ntt_layer_2_step_pre
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (zeta1: i16) (zeta2: i16) ->
        true);
    f_ntt_layer_2_step_post
    =
    (fun
        (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_ntt_layer_2_step
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (zeta1: i16) (zeta2: i16) ->
        Libcrux_polynomials_aarch64.Simd128ops.ntt_layer_2_step a zeta1 zeta2);
    f_ntt_layer_3_step_pre
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (zeta: i16) -> true);
    f_ntt_layer_3_step_post
    =
    (fun
        (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta: i16)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_ntt_layer_3_step
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (zeta: i16) ->
        Libcrux_polynomials_aarch64.Simd128ops.ntt_layer_3_step a zeta);
    f_inv_ntt_layer_1_step_pre
    =
    (fun
        (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        true);
    f_inv_ntt_layer_1_step_post
    =
    (fun
        (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_inv_ntt_layer_1_step
    =
    (fun
        (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        Libcrux_polynomials_aarch64.Simd128ops.inv_ntt_layer_1_step a zeta1 zeta2 zeta3 zeta4);
    f_inv_ntt_layer_2_step_pre
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (zeta1: i16) (zeta2: i16) ->
        true);
    f_inv_ntt_layer_2_step_post
    =
    (fun
        (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_inv_ntt_layer_2_step
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (zeta1: i16) (zeta2: i16) ->
        Libcrux_polynomials_aarch64.Simd128ops.inv_ntt_layer_2_step a zeta1 zeta2);
    f_inv_ntt_layer_3_step_pre
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (zeta: i16) -> true);
    f_inv_ntt_layer_3_step_post
    =
    (fun
        (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta: i16)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_inv_ntt_layer_3_step
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (zeta: i16) ->
        Libcrux_polynomials_aarch64.Simd128ops.inv_ntt_layer_3_step a zeta);
    f_ntt_multiply_pre
    =
    (fun
        (lhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (rhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        true);
    f_ntt_multiply_post
    =
    (fun
        (lhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (rhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        ->
        true);
    f_ntt_multiply
    =
    (fun
        (lhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (rhs: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (zeta4: i16)
        ->
        Libcrux_polynomials_aarch64.Simd128ops.ntt_multiply lhs rhs zeta1 zeta2 zeta3 zeta4);
    f_serialize_1_pre = (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_serialize_1_post
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (out: t_Array u8 (sz 2)) ->
        true);
    f_serialize_1_
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.serialize_1_ a);
    f_deserialize_1_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_1_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_deserialize_1_
    =
    (fun (a: t_Slice u8) -> Libcrux_polynomials_aarch64.Simd128ops.deserialize_1_ a);
    f_serialize_4_pre = (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_serialize_4_post
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (out: t_Array u8 (sz 8)) ->
        true);
    f_serialize_4_
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.serialize_4_ a);
    f_deserialize_4_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_4_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_deserialize_4_
    =
    (fun (a: t_Slice u8) -> Libcrux_polynomials_aarch64.Simd128ops.deserialize_4_ a);
    f_serialize_5_pre = (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_serialize_5_post
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (out: t_Array u8 (sz 10)) ->
        true);
    f_serialize_5_
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.serialize_5_ a);
    f_deserialize_5_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_5_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_deserialize_5_
    =
    (fun (a: t_Slice u8) -> Libcrux_polynomials_aarch64.Simd128ops.deserialize_5_ a);
    f_serialize_10_pre = (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_serialize_10_post
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (out: t_Array u8 (sz 20)) ->
        true);
    f_serialize_10_
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.serialize_10_ a);
    f_deserialize_10_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_10_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_deserialize_10_
    =
    (fun (a: t_Slice u8) -> Libcrux_polynomials_aarch64.Simd128ops.deserialize_10_ a);
    f_serialize_11_pre = (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_serialize_11_post
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (out: t_Array u8 (sz 22)) ->
        true);
    f_serialize_11_
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.serialize_11_ a);
    f_deserialize_11_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_11_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_deserialize_11_
    =
    (fun (a: t_Slice u8) -> Libcrux_polynomials_aarch64.Simd128ops.deserialize_11_ a);
    f_serialize_12_pre = (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_serialize_12_post
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) (out: t_Array u8 (sz 24)) ->
        true);
    f_serialize_12_
    =
    (fun (a: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) ->
        Libcrux_polynomials_aarch64.Simd128ops.serialize_12_ a);
    f_deserialize_12_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_12_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector) -> true);
    f_deserialize_12_
    =
    (fun (a: t_Slice u8) -> Libcrux_polynomials_aarch64.Simd128ops.deserialize_12_ a);
    f_rej_sample_pre = (fun (a: t_Slice u8) -> true);
    f_rej_sample_post = (fun (a: t_Slice u8) (out: (usize & t_Array i16 (sz 16))) -> true);
    f_rej_sample = fun (a: t_Slice u8) -> Libcrux_polynomials_aarch64.Rejsample.rej_sample a
  }
