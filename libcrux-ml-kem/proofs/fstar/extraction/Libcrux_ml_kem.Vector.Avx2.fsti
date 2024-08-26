module Libcrux_ml_kem.Vector.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

noeq

type t_SIMD256Vector = { f_elements:Libcrux_intrinsics.Avx2_extract.t_Vec256 }

val repr (x:t_SIMD256Vector) : t_Array i16 (sz 16)

val from_i16_array (array: t_Slice i16)
    : Prims.Pure t_SIMD256Vector
      Prims.l_True
      (ensures
        fun result ->
          let result:t_SIMD256Vector = result in
          repr result == array)

val to_i16_array (v: t_SIMD256Vector)
    : Prims.Pure (t_Array i16 (sz 16))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array i16 (sz 16) = result in
          result == repr v)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_kem.Vector.Traits.t_Repr t_SIMD256Vector =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    f_repr_pre = (fun (x: t_SIMD256Vector) -> true);
    f_repr_post = (fun (x: t_SIMD256Vector) (out: t_Array i16 (sz 16)) -> true);
    f_repr = fun (x: t_SIMD256Vector) -> to_i16_array x
  }

val zero: Prims.unit
  -> Prims.Pure t_SIMD256Vector
      Prims.l_True
      (ensures
        fun result ->
          let result:t_SIMD256Vector = result in
          to_i16_array result == Seq.create 16 0s)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Libcrux_ml_kem.Vector.Traits.t_Operations t_SIMD256Vector =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_8706949974463268012 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post
    =
    (fun (_: Prims.unit) (out: t_SIMD256Vector) -> impl.f_repr out == Seq.create 16 0s);
    f_ZERO = (fun (_: Prims.unit) -> zero ());
    f_from_i16_array_pre
    =
    (fun (array: t_Slice i16) -> (Core.Slice.impl__len #i16 array <: usize) =. sz 16);
    f_from_i16_array_post
    =
    (fun (array: t_Slice i16) (out: t_SIMD256Vector) -> impl.f_repr out == array);
    f_from_i16_array = (fun (array: t_Slice i16) -> from_i16_array array);
    f_to_i16_array_pre = (fun (x: t_SIMD256Vector) -> true);
    f_to_i16_array_post
    =
    (fun (x: t_SIMD256Vector) (out: t_Array i16 (sz 16)) -> out == impl.f_repr x);
    f_to_i16_array = (fun (x: t_SIMD256Vector) -> to_i16_array x);
    f_add_pre = (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) -> true);
    f_add_post
    =
    (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) (out: t_SIMD256Vector) ->
        impl.f_repr out == Spec.Utils.map2 ( +. ) (impl.f_repr lhs) (impl.f_repr rhs));
    f_add
    =
    (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Arithmetic.add lhs.f_elements rhs.f_elements }
        <:
        t_SIMD256Vector);
    f_sub_pre = (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) -> true);
    f_sub_post
    =
    (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) (out: t_SIMD256Vector) ->
        impl.f_repr out == Spec.Utils.map2 ( -. ) (impl.f_repr lhs) (impl.f_repr rhs));
    f_sub
    =
    (fun (lhs: t_SIMD256Vector) (rhs: t_SIMD256Vector) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Arithmetic.sub lhs.f_elements rhs.f_elements }
        <:
        t_SIMD256Vector);
    f_multiply_by_constant_pre = (fun (v: t_SIMD256Vector) (c: i16) -> true);
    f_multiply_by_constant_post
    =
    (fun (v: t_SIMD256Vector) (c: i16) (out: t_SIMD256Vector) ->
        impl.f_repr out == Spec.Utils.map_array (fun x -> x *. c) (impl.f_repr v));
    f_multiply_by_constant
    =
    (fun (v: t_SIMD256Vector) (c: i16) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Arithmetic.multiply_by_constant v.f_elements c }
        <:
        t_SIMD256Vector);
    f_bitwise_and_with_constant_pre = (fun (vector: t_SIMD256Vector) (constant: i16) -> true);
    f_bitwise_and_with_constant_post
    =
    (fun (vector: t_SIMD256Vector) (constant: i16) (out: t_SIMD256Vector) ->
        impl.f_repr out == Spec.Utils.map_array (fun x -> x &. constant) (impl.f_repr vector));
    f_bitwise_and_with_constant
    =
    (fun (vector: t_SIMD256Vector) (constant: i16) ->
        {
          f_elements
          =
          Libcrux_ml_kem.Vector.Avx2.Arithmetic.bitwise_and_with_constant vector.f_elements constant
        }
        <:
        t_SIMD256Vector);
    f_shift_right_pre
    =
    (fun (v_SHIFT_BY: i32) (vector: t_SIMD256Vector) -> v_SHIFT_BY >=. 0l && v_SHIFT_BY <. 16l);
    f_shift_right_post
    =
    (fun (v_SHIFT_BY: i32) (vector: t_SIMD256Vector) (out: t_SIMD256Vector) ->
        (v_SHIFT_BY >=. 0l /\ v_SHIFT_BY <. 16l) ==>
        impl.f_repr out == Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY) (impl.f_repr vector));
    f_shift_right
    =
    (fun (v_SHIFT_BY: i32) (vector: t_SIMD256Vector) ->
        {
          f_elements
          =
          Libcrux_ml_kem.Vector.Avx2.Arithmetic.shift_right v_SHIFT_BY vector.f_elements
        }
        <:
        t_SIMD256Vector);
    f_cond_subtract_3329_pre = (fun (vector: t_SIMD256Vector) -> true);
    f_cond_subtract_3329_post
    =
    (fun (vector: t_SIMD256Vector) (out: t_SIMD256Vector) ->
        impl.f_repr out ==
        Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x) (impl.f_repr vector));
    f_cond_subtract_3329_
    =
    (fun (vector: t_SIMD256Vector) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Arithmetic.cond_subtract_3329_ vector.f_elements }
        <:
        t_SIMD256Vector);
    f_barrett_reduce_pre = (fun (vector: t_SIMD256Vector) -> true);
    f_barrett_reduce_post = (fun (vector: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_barrett_reduce
    =
    (fun (vector: t_SIMD256Vector) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Arithmetic.barrett_reduce vector.f_elements }
        <:
        t_SIMD256Vector);
    f_montgomery_multiply_by_constant_pre = (fun (vector: t_SIMD256Vector) (constant: i16) -> true);
    f_montgomery_multiply_by_constant_post
    =
    (fun (vector: t_SIMD256Vector) (constant: i16) (out: t_SIMD256Vector) -> true);
    f_montgomery_multiply_by_constant
    =
    (fun (vector: t_SIMD256Vector) (constant: i16) ->
        {
          f_elements
          =
          Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_by_constant vector.f_elements
            constant
        }
        <:
        t_SIMD256Vector);
    f_compress_1_pre = (fun (vector: t_SIMD256Vector) -> true);
    f_compress_1_post = (fun (vector: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_compress_1_
    =
    (fun (vector: t_SIMD256Vector) ->
        {
          f_elements
          =
          Libcrux_ml_kem.Vector.Avx2.Compress.compress_message_coefficient vector.f_elements
        }
        <:
        t_SIMD256Vector);
    f_compress_pre = (fun (v_COEFFICIENT_BITS: i32) (vector: t_SIMD256Vector) -> true);
    f_compress_post
    =
    (fun (v_COEFFICIENT_BITS: i32) (vector: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_compress
    =
    (fun (v_COEFFICIENT_BITS: i32) (vector: t_SIMD256Vector) ->
        {
          f_elements
          =
          Libcrux_ml_kem.Vector.Avx2.Compress.compress_ciphertext_coefficient v_COEFFICIENT_BITS
            vector.f_elements
        }
        <:
        t_SIMD256Vector);
    f_decompress_ciphertext_coefficient_pre
    =
    (fun (v_COEFFICIENT_BITS: i32) (vector: t_SIMD256Vector) -> true);
    f_decompress_ciphertext_coefficient_post
    =
    (fun (v_COEFFICIENT_BITS: i32) (vector: t_SIMD256Vector) (out: t_SIMD256Vector) -> true);
    f_decompress_ciphertext_coefficient
    =
    (fun (v_COEFFICIENT_BITS: i32) (vector: t_SIMD256Vector) ->
        {
          f_elements
          =
          Libcrux_ml_kem.Vector.Avx2.Compress.decompress_ciphertext_coefficient v_COEFFICIENT_BITS
            vector.f_elements
        }
        <:
        t_SIMD256Vector);
    f_ntt_layer_1_step_pre
    =
    (fun (vector: t_SIMD256Vector) (zeta0: i16) (zeta1: i16) (zeta2: i16) (zeta3: i16) -> true);
    f_ntt_layer_1_step_post
    =
    (fun
        (vector: t_SIMD256Vector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: t_SIMD256Vector)
        ->
        true);
    f_ntt_layer_1_step
    =
    (fun (vector: t_SIMD256Vector) (zeta0: i16) (zeta1: i16) (zeta2: i16) (zeta3: i16) ->
        {
          f_elements
          =
          Libcrux_ml_kem.Vector.Avx2.Ntt.ntt_layer_1_step vector.f_elements zeta0 zeta1 zeta2 zeta3
        }
        <:
        t_SIMD256Vector);
    f_ntt_layer_2_step_pre = (fun (vector: t_SIMD256Vector) (zeta0: i16) (zeta1: i16) -> true);
    f_ntt_layer_2_step_post
    =
    (fun (vector: t_SIMD256Vector) (zeta0: i16) (zeta1: i16) (out: t_SIMD256Vector) -> true);
    f_ntt_layer_2_step
    =
    (fun (vector: t_SIMD256Vector) (zeta0: i16) (zeta1: i16) ->
        {
          f_elements = Libcrux_ml_kem.Vector.Avx2.Ntt.ntt_layer_2_step vector.f_elements zeta0 zeta1
        }
        <:
        t_SIMD256Vector);
    f_ntt_layer_3_step_pre = (fun (vector: t_SIMD256Vector) (zeta: i16) -> true);
    f_ntt_layer_3_step_post
    =
    (fun (vector: t_SIMD256Vector) (zeta: i16) (out: t_SIMD256Vector) -> true);
    f_ntt_layer_3_step
    =
    (fun (vector: t_SIMD256Vector) (zeta: i16) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Ntt.ntt_layer_3_step vector.f_elements zeta }
        <:
        t_SIMD256Vector);
    f_inv_ntt_layer_1_step_pre
    =
    (fun (vector: t_SIMD256Vector) (zeta0: i16) (zeta1: i16) (zeta2: i16) (zeta3: i16) -> true);
    f_inv_ntt_layer_1_step_post
    =
    (fun
        (vector: t_SIMD256Vector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: t_SIMD256Vector)
        ->
        true);
    f_inv_ntt_layer_1_step
    =
    (fun (vector: t_SIMD256Vector) (zeta0: i16) (zeta1: i16) (zeta2: i16) (zeta3: i16) ->
        {
          f_elements
          =
          Libcrux_ml_kem.Vector.Avx2.Ntt.inv_ntt_layer_1_step vector.f_elements
            zeta0
            zeta1
            zeta2
            zeta3
        }
        <:
        t_SIMD256Vector);
    f_inv_ntt_layer_2_step_pre = (fun (vector: t_SIMD256Vector) (zeta0: i16) (zeta1: i16) -> true);
    f_inv_ntt_layer_2_step_post
    =
    (fun (vector: t_SIMD256Vector) (zeta0: i16) (zeta1: i16) (out: t_SIMD256Vector) -> true);
    f_inv_ntt_layer_2_step
    =
    (fun (vector: t_SIMD256Vector) (zeta0: i16) (zeta1: i16) ->
        {
          f_elements
          =
          Libcrux_ml_kem.Vector.Avx2.Ntt.inv_ntt_layer_2_step vector.f_elements zeta0 zeta1
        }
        <:
        t_SIMD256Vector);
    f_inv_ntt_layer_3_step_pre = (fun (vector: t_SIMD256Vector) (zeta: i16) -> true);
    f_inv_ntt_layer_3_step_post
    =
    (fun (vector: t_SIMD256Vector) (zeta: i16) (out: t_SIMD256Vector) -> true);
    f_inv_ntt_layer_3_step
    =
    (fun (vector: t_SIMD256Vector) (zeta: i16) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Ntt.inv_ntt_layer_3_step vector.f_elements zeta }
        <:
        t_SIMD256Vector);
    f_ntt_multiply_pre
    =
    (fun
        (lhs: t_SIMD256Vector)
        (rhs: t_SIMD256Vector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        true);
    f_ntt_multiply_post
    =
    (fun
        (lhs: t_SIMD256Vector)
        (rhs: t_SIMD256Vector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: t_SIMD256Vector)
        ->
        true);
    f_ntt_multiply
    =
    (fun
        (lhs: t_SIMD256Vector)
        (rhs: t_SIMD256Vector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        {
          f_elements
          =
          Libcrux_ml_kem.Vector.Avx2.Ntt.ntt_multiply lhs.f_elements
            rhs.f_elements
            zeta0
            zeta1
            zeta2
            zeta3
        }
        <:
        t_SIMD256Vector);
    f_serialize_1_pre = (fun (vector: t_SIMD256Vector) -> true);
    f_serialize_1_post = (fun (vector: t_SIMD256Vector) (out: t_Array u8 (sz 2)) -> true);
    f_serialize_1_
    =
    (fun (vector: t_SIMD256Vector) ->
        Libcrux_ml_kem.Vector.Avx2.Serialize.serialize_1_ vector.f_elements);
    f_deserialize_1_pre = (fun (bytes: t_Slice u8) -> true);
    f_deserialize_1_post = (fun (bytes: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_1_
    =
    (fun (bytes: t_Slice u8) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Serialize.deserialize_1_ bytes }
        <:
        t_SIMD256Vector);
    f_serialize_4_pre = (fun (vector: t_SIMD256Vector) -> true);
    f_serialize_4_post = (fun (vector: t_SIMD256Vector) (out: t_Array u8 (sz 8)) -> true);
    f_serialize_4_
    =
    (fun (vector: t_SIMD256Vector) ->
        Libcrux_ml_kem.Vector.Avx2.Serialize.serialize_4_ vector.f_elements);
    f_deserialize_4_pre = (fun (bytes: t_Slice u8) -> true);
    f_deserialize_4_post = (fun (bytes: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_4_
    =
    (fun (bytes: t_Slice u8) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Serialize.deserialize_4_ bytes }
        <:
        t_SIMD256Vector);
    f_serialize_5_pre = (fun (vector: t_SIMD256Vector) -> true);
    f_serialize_5_post = (fun (vector: t_SIMD256Vector) (out: t_Array u8 (sz 10)) -> true);
    f_serialize_5_
    =
    (fun (vector: t_SIMD256Vector) ->
        Libcrux_ml_kem.Vector.Avx2.Serialize.serialize_5_ vector.f_elements);
    f_deserialize_5_pre = (fun (bytes: t_Slice u8) -> true);
    f_deserialize_5_post = (fun (bytes: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_5_
    =
    (fun (bytes: t_Slice u8) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Serialize.deserialize_5_ bytes }
        <:
        t_SIMD256Vector);
    f_serialize_10_pre = (fun (vector: t_SIMD256Vector) -> true);
    f_serialize_10_post = (fun (vector: t_SIMD256Vector) (out: t_Array u8 (sz 20)) -> true);
    f_serialize_10_
    =
    (fun (vector: t_SIMD256Vector) ->
        Libcrux_ml_kem.Vector.Avx2.Serialize.serialize_10_ vector.f_elements);
    f_deserialize_10_pre = (fun (bytes: t_Slice u8) -> true);
    f_deserialize_10_post = (fun (bytes: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_10_
    =
    (fun (bytes: t_Slice u8) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Serialize.deserialize_10_ bytes }
        <:
        t_SIMD256Vector);
    f_serialize_11_pre = (fun (vector: t_SIMD256Vector) -> true);
    f_serialize_11_post = (fun (vector: t_SIMD256Vector) (out: t_Array u8 (sz 22)) -> true);
    f_serialize_11_
    =
    (fun (vector: t_SIMD256Vector) ->
        Libcrux_ml_kem.Vector.Avx2.Serialize.serialize_11_ vector.f_elements);
    f_deserialize_11_pre = (fun (bytes: t_Slice u8) -> true);
    f_deserialize_11_post = (fun (bytes: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_11_
    =
    (fun (bytes: t_Slice u8) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Serialize.deserialize_11_ bytes }
        <:
        t_SIMD256Vector);
    f_serialize_12_pre = (fun (vector: t_SIMD256Vector) -> true);
    f_serialize_12_post = (fun (vector: t_SIMD256Vector) (out: t_Array u8 (sz 24)) -> true);
    f_serialize_12_
    =
    (fun (vector: t_SIMD256Vector) ->
        Libcrux_ml_kem.Vector.Avx2.Serialize.serialize_12_ vector.f_elements);
    f_deserialize_12_pre = (fun (bytes: t_Slice u8) -> true);
    f_deserialize_12_post = (fun (bytes: t_Slice u8) (out: t_SIMD256Vector) -> true);
    f_deserialize_12_
    =
    (fun (bytes: t_Slice u8) ->
        { f_elements = Libcrux_ml_kem.Vector.Avx2.Serialize.deserialize_12_ bytes }
        <:
        t_SIMD256Vector);
    f_rej_sample_pre = (fun (input: t_Slice u8) (output: t_Slice i16) -> true);
    f_rej_sample_post
    =
    (fun (input: t_Slice u8) (output: t_Slice i16) (out1: (t_Slice i16 & usize)) -> true);
    f_rej_sample
    =
    fun (input: t_Slice u8) (output: t_Slice i16) ->
      let tmp0, out:(t_Slice i16 & usize) =
        Libcrux_ml_kem.Vector.Avx2.Sampling.rejection_sample input output
      in
      let output:t_Slice i16 = tmp0 in
      let hax_temp_output:usize = out in
      output, hax_temp_output <: (t_Slice i16 & usize)
  }
