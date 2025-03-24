module Libcrux_ml_kem.Vector.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = mk_i16 1353

let v_FIELD_MODULUS: i16 = mk_i16 3329

let v_FIELD_ELEMENTS_IN_VECTOR: usize = mk_usize 16

let v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = mk_u32 62209

let v_BARRETT_SHIFT: i32 = mk_i32 26

let v_BARRETT_R: i32 = mk_i32 1 <<! v_BARRETT_SHIFT

class t_Repr (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_13011033735201511749:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9529721400157967266:Core.Clone.t_Clone v_Self;
  f_repr_pre:x: v_Self -> pred: Type0{true ==> pred};
  f_repr_post:v_Self -> t_Array i16 (mk_usize 16) -> Type0;
  f_repr:x0: v_Self
    -> Prims.Pure (t_Array i16 (mk_usize 16)) (f_repr_pre x0) (fun result -> f_repr_post x0 result)
}

class t_Operations (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_13011033735201511749:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9529721400157967266:Core.Clone.t_Clone v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12682756204189288427:t_Repr v_Self;
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
            f_repr result == Seq.create 16 (mk_i16 0)) };
  f_ZERO:x0: Prims.unit -> Prims.Pure v_Self (f_ZERO_pre x0) (fun result -> f_ZERO_post x0 result);
  f_from_i16_array_pre:array: t_Slice i16
    -> pred: Type0{(Core.Slice.impl__len #i16 array <: usize) =. mk_usize 16 ==> pred};
  f_from_i16_array_post:array: t_Slice i16 -> result: v_Self
    -> pred: Type0{pred ==> f_repr result == array};
  f_from_i16_array:x0: t_Slice i16
    -> Prims.Pure v_Self (f_from_i16_array_pre x0) (fun result -> f_from_i16_array_post x0 result);
  f_to_i16_array_pre:x: v_Self -> pred: Type0{true ==> pred};
  f_to_i16_array_post:x: v_Self -> result: t_Array i16 (mk_usize 16)
    -> pred: Type0{pred ==> f_repr x == result};
  f_to_i16_array:x0: v_Self
    -> Prims.Pure (t_Array i16 (mk_usize 16))
        (f_to_i16_array_pre x0)
        (fun result -> f_to_i16_array_post x0 result);
  f_from_bytes_pre:array: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 array <: usize) >=. mk_usize 32 ==> pred};
  f_from_bytes_post:t_Slice u8 -> v_Self -> Type0;
  f_from_bytes:x0: t_Slice u8
    -> Prims.Pure v_Self (f_from_bytes_pre x0) (fun result -> f_from_bytes_post x0 result);
  f_to_bytes_pre:x: v_Self -> bytes: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 bytes <: usize) >=. mk_usize 32 ==> pred};
  f_to_bytes_post:v_Self -> t_Slice u8 -> t_Slice u8 -> Type0;
  f_to_bytes:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8) (f_to_bytes_pre x0 x1) (fun result -> f_to_bytes_post x0 x1 result);
  f_add_pre:lhs: v_Self -> rhs: v_Self
    -> pred:
      Type0
        { (forall i.
              i < 16 ==>
              Spec.Utils.is_intb (pow2 15 - 1)
                (v (Seq.index (f_repr lhs) i) + v (Seq.index (f_repr rhs) i))) ==>
          pred };
  f_add_post:lhs: v_Self -> rhs: v_Self -> result: v_Self
    -> pred:
      Type0
        { pred ==>
          (forall i.
              i < 16 ==>
              (v (Seq.index (f_repr result) i) ==
                v (Seq.index (f_repr lhs) i) + v (Seq.index (f_repr rhs) i))) };
  f_add:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result);
  f_sub_pre:lhs: v_Self -> rhs: v_Self
    -> pred:
      Type0
        { (forall i.
              i < 16 ==>
              Spec.Utils.is_intb (pow2 15 - 1)
                (v (Seq.index (f_repr lhs) i) - v (Seq.index (f_repr rhs) i))) ==>
          pred };
  f_sub_post:lhs: v_Self -> rhs: v_Self -> result: v_Self
    -> pred:
      Type0
        { pred ==>
          (forall i.
              i < 16 ==>
              (v (Seq.index (f_repr result) i) ==
                v (Seq.index (f_repr lhs) i) - v (Seq.index (f_repr rhs) i))) };
  f_sub:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_sub_pre x0 x1) (fun result -> f_sub_post x0 x1 result);
  f_multiply_by_constant_pre:vec: v_Self -> c: i16
    -> pred:
      Type0
        { (forall i.
              i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index (f_repr vec) i) * v c)) ==>
          pred };
  f_multiply_by_constant_post:vec: v_Self -> c: i16 -> result: v_Self
    -> pred:
      Type0
        { pred ==>
          (forall i.
              i < 16 ==> (v (Seq.index (f_repr result) i) == v (Seq.index (f_repr vec) i) * v c)) };
  f_multiply_by_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_multiply_by_constant_pre x0 x1)
        (fun result -> f_multiply_by_constant_post x0 x1 result);
  f_cond_subtract_3329__pre:v: v_Self
    -> pred: Type0{Spec.Utils.is_i16b_array (pow2 12 - 1) (f_repr v) ==> pred};
  f_cond_subtract_3329__post:v: v_Self -> result: v_Self
    -> pred:
      Type0
        { pred ==>
          f_repr result ==
          Spec.Utils.map_array (fun x -> if x >=. (mk_i16 3329) then x -! (mk_i16 3329) else x)
            (f_repr v) };
  f_cond_subtract_3329_:x0: v_Self
    -> Prims.Pure v_Self
        (f_cond_subtract_3329__pre x0)
        (fun result -> f_cond_subtract_3329__post x0 result);
  f_barrett_reduce_pre:vector: v_Self
    -> pred: Type0{Spec.Utils.is_i16b_array 28296 (f_repr vector) ==> pred};
  f_barrett_reduce_post:v_Self -> v_Self -> Type0;
  f_barrett_reduce:x0: v_Self
    -> Prims.Pure v_Self (f_barrett_reduce_pre x0) (fun result -> f_barrett_reduce_post x0 result);
  f_montgomery_multiply_by_constant_pre:v: v_Self -> c: i16
    -> pred: Type0{Spec.Utils.is_i16b 1664 c ==> pred};
  f_montgomery_multiply_by_constant_post:v_Self -> i16 -> v_Self -> Type0;
  f_montgomery_multiply_by_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_montgomery_multiply_by_constant_pre x0 x1)
        (fun result -> f_montgomery_multiply_by_constant_post x0 x1 result);
  f_to_unsigned_representative_pre:a: v_Self
    -> pred: Type0{Spec.Utils.is_i16b_array 3328 (f_repr a) ==> pred};
  f_to_unsigned_representative_post:a: v_Self -> result: v_Self
    -> pred:
      Type0
        { pred ==>
          (forall (i: nat).
              i < 16 ==>
              (let x = Seq.index (f_repr a) i in
                let y = Seq.index (f_repr result) i in
                (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329)))) };
  f_to_unsigned_representative:x0: v_Self
    -> Prims.Pure v_Self
        (f_to_unsigned_representative_pre x0)
        (fun result -> f_to_unsigned_representative_post x0 result);
  f_compress_1__pre:a: v_Self
    -> pred:
      Type0
        { (forall (i: nat).
              i < 16 ==> v (Seq.index (f_repr a) i) >= 0 /\ v (Seq.index (f_repr a) i) < 3329) ==>
          pred };
  f_compress_1__post:a: v_Self -> result: v_Self
    -> pred: Type0{pred ==> (forall (i: nat). i < 16 ==> bounded (Seq.index (f_repr result) i) 1)};
  f_compress_1_:x0: v_Self
    -> Prims.Pure v_Self (f_compress_1__pre x0) (fun result -> f_compress_1__post x0 result);
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
  f_decompress_1__pre:a: v_Self
    -> pred:
      Type0
        { (forall (i: nat).
              i < 16 ==>
              (let x = Seq.index (f_repr a) i in
                (x == mk_i16 0 \/ x == mk_i16 1))) ==>
          pred };
  f_decompress_1__post:v_Self -> v_Self -> Type0;
  f_decompress_1_:x0: v_Self
    -> Prims.Pure v_Self (f_decompress_1__pre x0) (fun result -> f_decompress_1__post x0 result);
  f_decompress_ciphertext_coefficient_pre:v_COEFFICIENT_BITS: i32 -> a: v_Self
    -> pred:
      Type0
        { (v v_COEFFICIENT_BITS == 4 \/ v v_COEFFICIENT_BITS == 5 \/ v v_COEFFICIENT_BITS == 10 \/
            v v_COEFFICIENT_BITS == 11) /\
          (forall (i: nat).
              i < 16 ==>
              v (Seq.index (f_repr a) i) >= 0 /\
              v (Seq.index (f_repr a) i) < pow2 (v v_COEFFICIENT_BITS)) ==>
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
          Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
          Spec.Utils.is_i16b_array (11207 + 5 * 3328) (f_repr a) ==>
          pred };
  f_ntt_layer_1_step_post:
      a: v_Self ->
      zeta0: i16 ->
      zeta1: i16 ->
      zeta2: i16 ->
      zeta3: i16 ->
      out: v_Self
    -> pred: Type0{pred ==> Spec.Utils.is_i16b_array (11207 + 6 * 3328) (f_repr out)};
  f_ntt_layer_1_step:x0: v_Self -> x1: i16 -> x2: i16 -> x3: i16 -> x4: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_1_step_pre x0 x1 x2 x3 x4)
        (fun result -> f_ntt_layer_1_step_post x0 x1 x2 x3 x4 result);
  f_ntt_layer_2_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16
    -> pred:
      Type0
        { Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
          Spec.Utils.is_i16b_array (11207 + 4 * 3328) (f_repr a) ==>
          pred };
  f_ntt_layer_2_step_post:a: v_Self -> zeta0: i16 -> zeta1: i16 -> out: v_Self
    -> pred: Type0{pred ==> Spec.Utils.is_i16b_array (11207 + 5 * 3328) (f_repr out)};
  f_ntt_layer_2_step:x0: v_Self -> x1: i16 -> x2: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_2_step_pre x0 x1 x2)
        (fun result -> f_ntt_layer_2_step_post x0 x1 x2 result);
  f_ntt_layer_3_step_pre:a: v_Self -> zeta: i16
    -> pred:
      Type0
        { Spec.Utils.is_i16b 1664 zeta /\ Spec.Utils.is_i16b_array (11207 + 3 * 3328) (f_repr a) ==>
          pred };
  f_ntt_layer_3_step_post:a: v_Self -> zeta: i16 -> out: v_Self
    -> pred: Type0{pred ==> Spec.Utils.is_i16b_array (11207 + 4 * 3328) (f_repr out)};
  f_ntt_layer_3_step:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_3_step_pre x0 x1)
        (fun result -> f_ntt_layer_3_step_post x0 x1 result);
  f_inv_ntt_layer_1_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16 -> zeta2: i16 -> zeta3: i16
    -> pred:
      Type0
        { Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
          Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
          Spec.Utils.is_i16b_array (4 * 3328) (f_repr a) ==>
          pred };
  f_inv_ntt_layer_1_step_post:
      a: v_Self ->
      zeta0: i16 ->
      zeta1: i16 ->
      zeta2: i16 ->
      zeta3: i16 ->
      out: v_Self
    -> pred: Type0{pred ==> Spec.Utils.is_i16b_array 3328 (f_repr out)};
  f_inv_ntt_layer_1_step:x0: v_Self -> x1: i16 -> x2: i16 -> x3: i16 -> x4: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_1_step_pre x0 x1 x2 x3 x4)
        (fun result -> f_inv_ntt_layer_1_step_post x0 x1 x2 x3 x4 result);
  f_inv_ntt_layer_2_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16
    -> pred:
      Type0
        { Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
          Spec.Utils.is_i16b_array 3328 (f_repr a) ==>
          pred };
  f_inv_ntt_layer_2_step_post:a: v_Self -> zeta0: i16 -> zeta1: i16 -> out: v_Self
    -> pred: Type0{pred ==> Spec.Utils.is_i16b_array 3328 (f_repr out)};
  f_inv_ntt_layer_2_step:x0: v_Self -> x1: i16 -> x2: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_2_step_pre x0 x1 x2)
        (fun result -> f_inv_ntt_layer_2_step_post x0 x1 x2 result);
  f_inv_ntt_layer_3_step_pre:a: v_Self -> zeta: i16
    -> pred:
      Type0{Spec.Utils.is_i16b 1664 zeta /\ Spec.Utils.is_i16b_array 3328 (f_repr a) ==> pred};
  f_inv_ntt_layer_3_step_post:a: v_Self -> zeta: i16 -> out: v_Self
    -> pred: Type0{pred ==> Spec.Utils.is_i16b_array 3328 (f_repr out)};
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
          Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
          Spec.Utils.is_i16b_array 3328 (f_repr lhs) /\ Spec.Utils.is_i16b_array 3328 (f_repr rhs) ==>
          pred };
  f_ntt_multiply_post:
      lhs: v_Self ->
      rhs: v_Self ->
      zeta0: i16 ->
      zeta1: i16 ->
      zeta2: i16 ->
      zeta3: i16 ->
      out: v_Self
    -> pred: Type0{pred ==> Spec.Utils.is_i16b_array 3328 (f_repr out)};
  f_ntt_multiply:x0: v_Self -> x1: v_Self -> x2: i16 -> x3: i16 -> x4: i16 -> x5: i16
    -> Prims.Pure v_Self
        (f_ntt_multiply_pre x0 x1 x2 x3 x4 x5)
        (fun result -> f_ntt_multiply_post x0 x1 x2 x3 x4 x5 result);
  f_serialize_1__pre:a: v_Self -> pred: Type0{Spec.MLKEM.serialize_pre 1 (f_repr a) ==> pred};
  f_serialize_1__post:a: v_Self -> result: t_Array u8 (mk_usize 2)
    -> pred:
      Type0
        { pred ==>
          Spec.MLKEM.serialize_pre 1 (f_repr a) ==> Spec.MLKEM.serialize_post 1 (f_repr a) result };
  f_serialize_1_:x0: v_Self
    -> Prims.Pure (t_Array u8 (mk_usize 2))
        (f_serialize_1__pre x0)
        (fun result -> f_serialize_1__post x0 result);
  f_deserialize_1__pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. mk_usize 2 ==> pred};
  f_deserialize_1__post:a: t_Slice u8 -> result: v_Self
    -> pred:
      Type0{pred ==> sz (Seq.length a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 a (f_repr result)};
  f_deserialize_1_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_1__pre x0) (fun result -> f_deserialize_1__post x0 result);
  f_serialize_4__pre:a: v_Self -> pred: Type0{Spec.MLKEM.serialize_pre 4 (f_repr a) ==> pred};
  f_serialize_4__post:a: v_Self -> result: t_Array u8 (mk_usize 8)
    -> pred:
      Type0
        { pred ==>
          Spec.MLKEM.serialize_pre 4 (f_repr a) ==> Spec.MLKEM.serialize_post 4 (f_repr a) result };
  f_serialize_4_:x0: v_Self
    -> Prims.Pure (t_Array u8 (mk_usize 8))
        (f_serialize_4__pre x0)
        (fun result -> f_serialize_4__post x0 result);
  f_deserialize_4__pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. mk_usize 8 ==> pred};
  f_deserialize_4__post:a: t_Slice u8 -> result: v_Self
    -> pred:
      Type0{pred ==> sz (Seq.length a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 a (f_repr result)};
  f_deserialize_4_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_4__pre x0) (fun result -> f_deserialize_4__post x0 result);
  f_serialize_5__pre:v_Self -> Type0;
  f_serialize_5__post:v_Self -> t_Array u8 (mk_usize 10) -> Type0;
  f_serialize_5_:x0: v_Self
    -> Prims.Pure (t_Array u8 (mk_usize 10))
        (f_serialize_5__pre x0)
        (fun result -> f_serialize_5__post x0 result);
  f_deserialize_5__pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. mk_usize 10 ==> pred};
  f_deserialize_5__post:t_Slice u8 -> v_Self -> Type0;
  f_deserialize_5_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_5__pre x0) (fun result -> f_deserialize_5__post x0 result);
  f_serialize_10__pre:a: v_Self -> pred: Type0{Spec.MLKEM.serialize_pre 10 (f_repr a) ==> pred};
  f_serialize_10__post:a: v_Self -> result: t_Array u8 (mk_usize 20)
    -> pred:
      Type0
        { pred ==>
          Spec.MLKEM.serialize_pre 10 (f_repr a) ==> Spec.MLKEM.serialize_post 10 (f_repr a) result
        };
  f_serialize_10_:x0: v_Self
    -> Prims.Pure (t_Array u8 (mk_usize 20))
        (f_serialize_10__pre x0)
        (fun result -> f_serialize_10__post x0 result);
  f_deserialize_10__pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. mk_usize 20 ==> pred};
  f_deserialize_10__post:a: t_Slice u8 -> result: v_Self
    -> pred:
      Type0
        {pred ==> sz (Seq.length a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 a (f_repr result)};
  f_deserialize_10_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_10__pre x0) (fun result -> f_deserialize_10__post x0 result);
  f_serialize_11__pre:v_Self -> Type0;
  f_serialize_11__post:v_Self -> t_Array u8 (mk_usize 22) -> Type0;
  f_serialize_11_:x0: v_Self
    -> Prims.Pure (t_Array u8 (mk_usize 22))
        (f_serialize_11__pre x0)
        (fun result -> f_serialize_11__post x0 result);
  f_deserialize_11__pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. mk_usize 22 ==> pred};
  f_deserialize_11__post:t_Slice u8 -> v_Self -> Type0;
  f_deserialize_11_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_11__pre x0) (fun result -> f_deserialize_11__post x0 result);
  f_serialize_12__pre:a: v_Self -> pred: Type0{Spec.MLKEM.serialize_pre 12 (f_repr a) ==> pred};
  f_serialize_12__post:a: v_Self -> result: t_Array u8 (mk_usize 24)
    -> pred:
      Type0
        { pred ==>
          Spec.MLKEM.serialize_pre 12 (f_repr a) ==> Spec.MLKEM.serialize_post 12 (f_repr a) result
        };
  f_serialize_12_:x0: v_Self
    -> Prims.Pure (t_Array u8 (mk_usize 24))
        (f_serialize_12__pre x0)
        (fun result -> f_serialize_12__post x0 result);
  f_deserialize_12__pre:a: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 a <: usize) =. mk_usize 24 ==> pred};
  f_deserialize_12__post:a: t_Slice u8 -> result: v_Self
    -> pred:
      Type0
        {pred ==> sz (Seq.length a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 a (f_repr result)};
  f_deserialize_12_:x0: t_Slice u8
    -> Prims.Pure v_Self (f_deserialize_12__pre x0) (fun result -> f_deserialize_12__post x0 result);
  f_rej_sample_pre:a: t_Slice u8 -> out: t_Slice i16
    -> pred:
      Type0
        { (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 24 &&
          (Core.Slice.impl__len #i16 out <: usize) =. mk_usize 16 ==>
          pred };
  f_rej_sample_post:a: t_Slice u8 -> out: t_Slice i16 -> x: (t_Slice i16 & usize)
    -> pred:
      Type0
        { pred ==>
          (let out_future, result:(t_Slice i16 & usize) = x in
            Seq.length out_future == Seq.length out /\ v result <= 16) };
  f_rej_sample:x0: t_Slice u8 -> x1: t_Slice i16
    -> Prims.Pure (t_Slice i16 & usize)
        (f_rej_sample_pre x0 x1)
        (fun result -> f_rej_sample_post x0 x1 result)
}
