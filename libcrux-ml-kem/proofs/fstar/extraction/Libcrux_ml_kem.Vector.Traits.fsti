module Libcrux_ml_kem.Vector.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Repr (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11581440318597584651:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9442900250278684536:Core.Clone.t_Clone v_Self;
  f_repr_pre:x: v_Self -> pred: Type0{true ==> pred};
  f_repr_post:v_Self -> t_Array i16 (sz 16) -> Type0;
  f_repr:x0: v_Self
    -> Prims.Pure (t_Array i16 (sz 16)) (f_repr_pre x0) (fun result -> f_repr_post x0 result)
}

class t_Operations (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11581440318597584651:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9442900250278684536:Core.Clone.t_Clone v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_8706949974463268012:t_Repr v_Self;
  f_ZERO_pre:x: Prims.unit
    -> pred:
      Type0
        { (let _:Prims.unit = x in
            true) ==>
          pred };
  f_ZERO_post:x: Prims.unit -> result: v_Self
    -> pred:
      Type0
        { pred ==>
          (let _:Prims.unit = x in
            f_repr result == Seq.create 16 0s) };
  f_ZERO:x0: Prims.unit -> Prims.Pure v_Self (f_ZERO_pre x0) (fun result -> f_ZERO_post x0 result);
  f_from_i16_array_pre:array: t_Slice i16
    -> pred: Type0{(Core.Slice.impl__len #i16 array <: usize) =. sz 16 ==> pred};
  f_from_i16_array_post:array: t_Slice i16 -> result: v_Self
    -> pred: Type0{pred ==> f_repr result == array};
  f_from_i16_array:x0: t_Slice i16
    -> Prims.Pure v_Self (f_from_i16_array_pre x0) (fun result -> f_from_i16_array_post x0 result);
  f_to_i16_array_pre:x: v_Self -> pred: Type0{true ==> pred};
  f_to_i16_array_post:x: v_Self -> result: t_Array i16 (sz 16)
    -> pred: Type0{pred ==> f_repr x == result};
  f_to_i16_array:x0: v_Self
    -> Prims.Pure (t_Array i16 (sz 16))
        (f_to_i16_array_pre x0)
        (fun result -> f_to_i16_array_post x0 result);
  f_add_pre:lhs: v_Self -> rhs: v_Self -> pred: Type0{true ==> pred};
  f_add_post:lhs: v_Self -> rhs: v_Self -> result: v_Self
    -> pred: Type0{pred ==> f_repr result == Spec.Utils.map2 ( +. ) (f_repr lhs) (f_repr rhs)};
  f_add:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result);
  f_sub_pre:lhs: v_Self -> rhs: v_Self -> pred: Type0{true ==> pred};
  f_sub_post:lhs: v_Self -> rhs: v_Self -> result: v_Self
    -> pred: Type0{pred ==> f_repr result == Spec.Utils.map2 ( -. ) (f_repr lhs) (f_repr rhs)};
  f_sub:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_sub_pre x0 x1) (fun result -> f_sub_post x0 x1 result);
  f_multiply_by_constant_pre:v: v_Self -> c: i16 -> pred: Type0{true ==> pred};
  f_multiply_by_constant_post:v: v_Self -> c: i16 -> result: v_Self
    -> pred: Type0{pred ==> f_repr result == Spec.Utils.map_array (fun x -> x *. c) (f_repr v)};
  f_multiply_by_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_multiply_by_constant_pre x0 x1)
        (fun result -> f_multiply_by_constant_post x0 x1 result);
  f_bitwise_and_with_constant_pre:v: v_Self -> c: i16 -> pred: Type0{true ==> pred};
  f_bitwise_and_with_constant_post:v: v_Self -> c: i16 -> result: v_Self
    -> pred: Type0{pred ==> f_repr result == Spec.Utils.map_array (fun x -> x &. c) (f_repr v)};
  f_bitwise_and_with_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_bitwise_and_with_constant_pre x0 x1)
        (fun result -> f_bitwise_and_with_constant_post x0 x1 result);
  f_shift_right_pre:v_SHIFT_BY: i32 -> v: v_Self
    -> pred: Type0{v_SHIFT_BY >=. 0l && v_SHIFT_BY <. 16l ==> pred};
  f_shift_right_post:v_SHIFT_BY: i32 -> v: v_Self -> result: v_Self
    -> pred:
      Type0
        { pred ==>
          (v_SHIFT_BY >=. 0l /\ v_SHIFT_BY <. 16l) ==>
          f_repr result == Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY) (f_repr v) };
  f_shift_right:v_SHIFT_BY: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_shift_right_pre v_SHIFT_BY x0)
        (fun result -> f_shift_right_post v_SHIFT_BY x0 result);
  f_cond_subtract_3329_pre:v: v_Self -> pred: Type0{true ==> pred};
  f_cond_subtract_3329_post:v: v_Self -> result: v_Self
    -> pred:
      Type0
        { pred ==>
          f_repr result ==
          Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x) (f_repr v) };
  f_cond_subtract_3329_:x0: v_Self
    -> Prims.Pure v_Self
        (f_cond_subtract_3329_pre x0)
        (fun result -> f_cond_subtract_3329_post x0 result);
  f_barrett_reduce_pre:vector: v_Self
    -> pred: Type0{Spec.Utils.is_i16b_array 28296 (f_repr vector) ==> pred};
  f_barrett_reduce_post:v_Self -> v_Self -> Type0;
  f_barrett_reduce:x0: v_Self
    -> Prims.Pure v_Self (f_barrett_reduce_pre x0) (fun result -> f_barrett_reduce_post x0 result);
  f_montgomery_multiply_by_constant_pre:v: v_Self -> c: i16
    -> pred: Type0{Spec.Utils.is_i16b 3328 c ==> pred};
  f_montgomery_multiply_by_constant_post:v_Self -> i16 -> v_Self -> Type0;
  f_montgomery_multiply_by_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_montgomery_multiply_by_constant_pre x0 x1)
        (fun result -> f_montgomery_multiply_by_constant_post x0 x1 result);
  f_compress_1_pre:a: v_Self
    -> pred:
      Type0
        { (forall (i: nat).
              i < 16 ==> v (Seq.index (f_repr a) i) >= 0 /\ v (Seq.index (f_repr a) i) < 3329) ==>
          pred };
  f_compress_1_post:a: v_Self -> result: v_Self
    -> pred: Type0{pred ==> (forall (i: nat). i < 16 ==> bounded (Seq.index (f_repr result) i) 1)};
  f_compress_1_:x0: v_Self
    -> Prims.Pure v_Self (f_compress_1_pre x0) (fun result -> f_compress_1_post x0 result);
  f_compress_pre:v_COEFFICIENT_BITS: i32 -> a: v_Self
    -> pred:
      Type0
        { (v v_COEFFICIENT_BITS == 4 \/ v v_COEFFICIENT_BITS == 5 \/ v v_COEFFICIENT_BITS == 10 \/
            v v_COEFFICIENT_BITS == 11) /\
          (forall (i: nat).
              i < 16 ==> v (Seq.index (f_repr a) i) >= 0 /\ v (Seq.index (f_repr a) i) < 3329) ==>
          pred };
  f_compress_post:v_COEFFICIENT_BITS: i32 -> a: v_Self -> result: v_Self
    -> pred:
      Type0
        { pred ==>
          (v v_COEFFICIENT_BITS == 4 \/ v v_COEFFICIENT_BITS == 5 \/ v v_COEFFICIENT_BITS == 10 \/
            v v_COEFFICIENT_BITS == 11) ==>
          (forall (i: nat). i < 16 ==> bounded (Seq.index (f_repr result) i) (v v_COEFFICIENT_BITS))
        };
  f_compress:v_COEFFICIENT_BITS: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_compress_pre v_COEFFICIENT_BITS x0)
        (fun result -> f_compress_post v_COEFFICIENT_BITS x0 result);
  f_decompress_ciphertext_coefficient_pre:v_COEFFICIENT_BITS: i32 -> v: v_Self
    -> pred:
      Type0
        { v_COEFFICIENT_BITS =. 4l || v_COEFFICIENT_BITS =. 5l || v_COEFFICIENT_BITS =. 10l ||
          v_COEFFICIENT_BITS =. 11l ==>
          pred };
  f_decompress_ciphertext_coefficient_post:v_COEFFICIENT_BITS: i32 -> v_Self -> v_Self -> Type0;
  f_decompress_ciphertext_coefficient:v_COEFFICIENT_BITS: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_decompress_ciphertext_coefficient_pre v_COEFFICIENT_BITS x0)
        (fun result -> f_decompress_ciphertext_coefficient_post v_COEFFICIENT_BITS x0 result);
  f_ntt_layer_1_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16 -> zeta2: i16 -> zeta3: i16
    -> pred:
      Type0
        { Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
          Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 ==>
          pred };
  f_ntt_layer_1_step_post:v_Self -> i16 -> i16 -> i16 -> i16 -> v_Self -> Type0;
  f_ntt_layer_1_step:x0: v_Self -> x1: i16 -> x2: i16 -> x3: i16 -> x4: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_1_step_pre x0 x1 x2 x3 x4)
        (fun result -> f_ntt_layer_1_step_post x0 x1 x2 x3 x4 result);
  f_ntt_layer_2_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16
    -> pred: Type0{Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 ==> pred};
  f_ntt_layer_2_step_post:v_Self -> i16 -> i16 -> v_Self -> Type0;
  f_ntt_layer_2_step:x0: v_Self -> x1: i16 -> x2: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_2_step_pre x0 x1 x2)
        (fun result -> f_ntt_layer_2_step_post x0 x1 x2 result);
  f_ntt_layer_3_step_pre:a: v_Self -> zeta: i16
    -> pred: Type0{Spec.Utils.is_i16b 1664 zeta ==> pred};
  f_ntt_layer_3_step_post:v_Self -> i16 -> v_Self -> Type0;
  f_ntt_layer_3_step:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_3_step_pre x0 x1)
        (fun result -> f_ntt_layer_3_step_post x0 x1 result);
  f_inv_ntt_layer_1_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16 -> zeta2: i16 -> zeta3: i16
    -> pred:
      Type0
        { Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
          Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 ==>
          pred };
  f_inv_ntt_layer_1_step_post:v_Self -> i16 -> i16 -> i16 -> i16 -> v_Self -> Type0;
  f_inv_ntt_layer_1_step:x0: v_Self -> x1: i16 -> x2: i16 -> x3: i16 -> x4: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_1_step_pre x0 x1 x2 x3 x4)
        (fun result -> f_inv_ntt_layer_1_step_post x0 x1 x2 x3 x4 result);
  f_inv_ntt_layer_2_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16
    -> pred: Type0{Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 ==> pred};
  f_inv_ntt_layer_2_step_post:v_Self -> i16 -> i16 -> v_Self -> Type0;
  f_inv_ntt_layer_2_step:x0: v_Self -> x1: i16 -> x2: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_2_step_pre x0 x1 x2)
        (fun result -> f_inv_ntt_layer_2_step_post x0 x1 x2 result);
  f_inv_ntt_layer_3_step_pre:a: v_Self -> zeta: i16
    -> pred: Type0{Spec.Utils.is_i16b 1664 zeta ==> pred};
  f_inv_ntt_layer_3_step_post:v_Self -> i16 -> v_Self -> Type0;
  f_inv_ntt_layer_3_step:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_3_step_pre x0 x1)
        (fun result -> f_inv_ntt_layer_3_step_post x0 x1 result);
  f_ntt_multiply_pre:
      lhs: v_Self ->
      rhs: v_Self ->
      zeta0: i16 ->
      zeta1: i16 ->
      zeta2: i16 ->
      zeta3: i16
    -> pred:
      Type0
        { Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
          Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 ==>
          pred };
  f_ntt_multiply_post:v_Self -> v_Self -> i16 -> i16 -> i16 -> i16 -> v_Self -> Type0;
  f_ntt_multiply:x0: v_Self -> x1: v_Self -> x2: i16 -> x3: i16 -> x4: i16 -> x5: i16
    -> Prims.Pure v_Self
        (f_ntt_multiply_pre x0 x1 x2 x3 x4 x5)
        (fun result -> f_ntt_multiply_post x0 x1 x2 x3 x4 x5 result);
  f_serialize_1_pre:a: v_Self -> pred: Type0{Spec.MLKEM.serialize_pre 1 (f_repr a) ==> pred};
  f_serialize_1_post:a: v_Self -> result: t_Array u8 (sz 2)
    -> pred:
      Type0
        { pred ==>
          Spec.MLKEM.serialize_pre 1 (f_repr a) ==> Spec.MLKEM.serialize_post 1 (f_repr a) result };
  f_serialize_1_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 2))
        (f_serialize_1_pre x0)
        (fun result -> f_serialize_1_post x0 result);
  f_deserialize_1_pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. sz 2 ==> pred};
  f_deserialize_1_post:a: t_Slice u8 -> result: v_Self
    -> pred:
      Type0{pred ==> sz (Seq.length a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 a (f_repr result)};
  f_deserialize_1_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_1_pre x0) (fun result -> f_deserialize_1_post x0 result);
  f_serialize_4_pre:a: v_Self -> pred: Type0{Spec.MLKEM.serialize_pre 4 (f_repr a) ==> pred};
  f_serialize_4_post:a: v_Self -> result: t_Array u8 (sz 8)
    -> pred:
      Type0
        { pred ==>
          Spec.MLKEM.serialize_pre 4 (f_repr a) ==> Spec.MLKEM.serialize_post 4 (f_repr a) result };
  f_serialize_4_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 8))
        (f_serialize_4_pre x0)
        (fun result -> f_serialize_4_post x0 result);
  f_deserialize_4_pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. sz 8 ==> pred};
  f_deserialize_4_post:a: t_Slice u8 -> result: v_Self
    -> pred:
      Type0{pred ==> sz (Seq.length a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 a (f_repr result)};
  f_deserialize_4_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_4_pre x0) (fun result -> f_deserialize_4_post x0 result);
  f_serialize_5_pre:v_Self -> Type0;
  f_serialize_5_post:v_Self -> t_Array u8 (sz 10) -> Type0;
  f_serialize_5_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 10))
        (f_serialize_5_pre x0)
        (fun result -> f_serialize_5_post x0 result);
  f_deserialize_5_pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. sz 10 ==> pred};
  f_deserialize_5_post:t_Slice u8 -> v_Self -> Type0;
  f_deserialize_5_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_5_pre x0) (fun result -> f_deserialize_5_post x0 result);
  f_serialize_10_pre:a: v_Self -> pred: Type0{Spec.MLKEM.serialize_pre 10 (f_repr a) ==> pred};
  f_serialize_10_post:a: v_Self -> result: t_Array u8 (sz 20)
    -> pred:
      Type0
        { pred ==>
          Spec.MLKEM.serialize_pre 10 (f_repr a) ==> Spec.MLKEM.serialize_post 10 (f_repr a) result
        };
  f_serialize_10_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 20))
        (f_serialize_10_pre x0)
        (fun result -> f_serialize_10_post x0 result);
  f_deserialize_10_pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. sz 20 ==> pred};
  f_deserialize_10_post:a: t_Slice u8 -> result: v_Self
    -> pred:
      Type0
        {pred ==> sz (Seq.length a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 a (f_repr result)};
  f_deserialize_10_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_10_pre x0) (fun result -> f_deserialize_10_post x0 result);
  f_serialize_11_pre:v_Self -> Type0;
  f_serialize_11_post:v_Self -> t_Array u8 (sz 22) -> Type0;
  f_serialize_11_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 22))
        (f_serialize_11_pre x0)
        (fun result -> f_serialize_11_post x0 result);
  f_deserialize_11_pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. sz 22 ==> pred};
  f_deserialize_11_post:t_Slice u8 -> v_Self -> Type0;
  f_deserialize_11_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_11_pre x0) (fun result -> f_deserialize_11_post x0 result);
  f_serialize_12_pre:a: v_Self -> pred: Type0{Spec.MLKEM.serialize_pre 12 (f_repr a) ==> pred};
  f_serialize_12_post:a: v_Self -> result: t_Array u8 (sz 24)
    -> pred:
      Type0
        { pred ==>
          Spec.MLKEM.serialize_pre 12 (f_repr a) ==> Spec.MLKEM.serialize_post 12 (f_repr a) result
        };
  f_serialize_12_:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 24))
        (f_serialize_12_pre x0)
        (fun result -> f_serialize_12_post x0 result);
  f_deserialize_12_pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. sz 24 ==> pred};
  f_deserialize_12_post:a: t_Slice u8 -> result: v_Self
    -> pred:
      Type0
        {pred ==> sz (Seq.length a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 a (f_repr result)};
  f_deserialize_12_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_12_pre x0) (fun result -> f_deserialize_12_post x0 result);
  f_rej_sample_pre:a: t_Slice u8 -> out: t_Slice i16 -> pred: Type0{true ==> pred};
  f_rej_sample_post:a: t_Slice u8 -> out: t_Slice i16 -> x: (t_Slice i16 & usize)
    -> pred:
      Type0
        { pred ==>
          (let out_future, result:(t_Slice i16 & usize) = x in
            Seq.length out_future == Seq.length out /\ range (v result + 255) usize_inttype) };
  f_rej_sample:x0: t_Slice u8 -> x1: t_Slice i16
    -> Prims.Pure (t_Slice i16 & usize)
        (f_rej_sample_pre x0 x1)
        (fun result -> f_rej_sample_post x0 x1 result)
}

/// Internal vectors.
/// Used in the unpacked API.
class t_VectorType (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_14104493667227926613:t_Operations v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_T)
    : t_VectorType v_T = { _super_14104493667227926613 = FStar.Tactics.Typeclasses.solve }

let v_BARRETT_SHIFT: i32 = 26l

let v_BARRETT_R: i32 = 1l <<! v_BARRETT_SHIFT

let v_FIELD_ELEMENTS_IN_VECTOR: usize = sz 16

let v_FIELD_MODULUS: i16 = 3329s

let v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209ul

let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353s

val decompress_1_ (#v_T: Type0) {| i1: t_Operations v_T |} (v: v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_fe (#v_T: Type0) {| i1: t_Operations v_T |} (v: v_T) (fer: i16)
    : Prims.Pure v_T (requires Spec.Utils.is_i16b 3328 fer) (fun _ -> Prims.l_True)

val to_standard_domain (#v_T: Type0) {| i1: t_Operations v_T |} (v: v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val to_unsigned_representative (#v_T: Type0) {| i1: t_Operations v_T |} (a: v_T)
    : Prims.Pure v_T
      Prims.l_True
      (ensures
        fun result ->
          let result:v_T = result in
          f_to_i16_array result ==
          Spec.Utils.map2 ( +. )
            (f_to_i16_array a)
            (Spec.Utils.map_array (fun x -> (x >>! 15l) &. v_FIELD_MODULUS) (f_to_i16_array a)))
