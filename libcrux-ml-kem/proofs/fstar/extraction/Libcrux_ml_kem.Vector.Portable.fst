module Libcrux_ml_kem.Vector.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable.Vector_type in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_kem.Vector.Traits.t_Repr
Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
  {
    _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve;
    _super_9529721400157967266 = FStar.Tactics.Typeclasses.solve;
    f_repr_pre = (fun (x: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_repr_post
    =
    (fun
        (x: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Array i16 (mk_usize 16))
        ->
        true);
    f_repr
    =
    fun (x: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
      Libcrux_ml_kem.Vector.Portable.Vector_type.to_i16_array x
  }

let serialize_1_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let _:Prims.unit = assert (forall i. Rust_primitives.bounded (Seq.index a.f_elements i) 1) in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.serialize_1_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_1_ a

let deserialize_1_ (a: t_Slice u8) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_lemma a in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_bounded_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_ a

let serialize_4_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let _:Prims.unit = assert (forall i. Rust_primitives.bounded (Seq.index a.f_elements i) 4) in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.serialize_4_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_4_ a

let deserialize_4_ (a: t_Slice u8) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_lemma a in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_bounded_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_ a

let serialize_5_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_5_ a

let deserialize_5_ (a: t_Slice u8) = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_5_ a

let serialize_10_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.serialize_10_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_10_ a

let deserialize_10_ (a: t_Slice u8) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_lemma a in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_bounded_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_ a

let serialize_11_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_11_ a

let deserialize_11_ (a: t_Slice u8) = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_11_ a

let serialize_12_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.serialize_12_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_12_ a

let deserialize_12_ (a: t_Slice u8) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_lemma a in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_bounded_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_ a

#push-options "--z3rlimit 400 --split_queries always"

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Libcrux_ml_kem.Vector.Traits.t_Operations
Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
  {
    _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve;
    _super_9529721400157967266 = FStar.Tactics.Typeclasses.solve;
    _super_12682756204189288427 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post
    =
    (fun (_: Prims.unit) (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        impl.f_repr out == Seq.create 16 (mk_i16 0));
    f_ZERO = (fun (_: Prims.unit) -> Libcrux_ml_kem.Vector.Portable.Vector_type.zero ());
    f_from_i16_array_pre
    =
    (fun (array: t_Slice i16) -> (Core.Slice.impl__len #i16 array <: usize) =. mk_usize 16);
    f_from_i16_array_post
    =
    (fun (array: t_Slice i16) (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        impl.f_repr out == array);
    f_from_i16_array
    =
    (fun (array: t_Slice i16) -> Libcrux_ml_kem.Vector.Portable.Vector_type.from_i16_array array);
    f_to_i16_array_pre
    =
    (fun (x: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_to_i16_array_post
    =
    (fun
        (x: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Array i16 (mk_usize 16))
        ->
        out == impl.f_repr x);
    f_to_i16_array
    =
    (fun (x: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        Libcrux_ml_kem.Vector.Portable.Vector_type.to_i16_array x);
    f_add_pre
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Libcrux_ml_kem.Vector.Traits.add_pre lhs.f_elements rhs.f_elements);
    f_add_post
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (result: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Libcrux_ml_kem.Vector.Traits.add_post lhs.f_elements rhs.f_elements result.f_elements);
    f_add
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        let _:Prims.unit =
          reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.add_pre)
            Libcrux_ml_kem.Vector.Traits.add_pre;
          reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.add_post)
            Libcrux_ml_kem.Vector.Traits.add_post
        in
        Libcrux_ml_kem.Vector.Portable.Arithmetic.add lhs rhs);
    f_sub_pre
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Libcrux_ml_kem.Vector.Traits.sub_pre lhs.f_elements rhs.f_elements);
    f_sub_post
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (result: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Libcrux_ml_kem.Vector.Traits.sub_post lhs.f_elements rhs.f_elements result.f_elements);
    f_sub
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        let _:Prims.unit =
          reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.sub_pre)
            Libcrux_ml_kem.Vector.Traits.sub_pre;
          reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.sub_post)
            Libcrux_ml_kem.Vector.Traits.sub_post
        in
        Libcrux_ml_kem.Vector.Portable.Arithmetic.sub lhs rhs);
    f_multiply_by_constant_pre
    =
    (fun (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16) ->
        forall i. i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index vec.f_elements i) * v c)
    );
    f_multiply_by_constant_post
    =
    (fun
        (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (c: i16)
        (result: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        forall i.
          i < 16 ==> (v (Seq.index result.f_elements i) == v (Seq.index vec.f_elements i) * v c));
    f_multiply_by_constant
    =
    (fun (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16) ->
        Libcrux_ml_kem.Vector.Portable.Arithmetic.multiply_by_constant vec c);
    f_bitwise_and_with_constant_pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16) -> true);
    f_bitwise_and_with_constant_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (c: i16)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        impl.f_repr out == Spec.Utils.map_array (fun x -> x &. c) (impl.f_repr v));
    f_bitwise_and_with_constant
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16) ->
        Libcrux_ml_kem.Vector.Portable.Arithmetic.bitwise_and_with_constant v c);
    f_shift_right_pre
    =
    (fun (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 16);
    f_shift_right_post
    =
    (fun
        (v_SHIFT_BY: i32)
        (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        (v_SHIFT_BY >=. (mk_i32 0) /\ v_SHIFT_BY <. (mk_i32 16)) ==>
        impl.f_repr out == Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY) (impl.f_repr v));
    f_shift_right
    =
    (fun (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        Libcrux_ml_kem.Vector.Portable.Arithmetic.shift_right v_SHIFT_BY v);
    f_cond_subtract_3329__pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        Spec.Utils.is_i16b_array (pow2 12 - 1) (impl.f_repr v));
    f_cond_subtract_3329__post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        impl.f_repr out ==
        Spec.Utils.map_array (fun x -> if x >=. (mk_i16 3329) then x -! (mk_i16 3329) else x)
          (impl.f_repr v));
    f_cond_subtract_3329_
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        Libcrux_ml_kem.Vector.Portable.Arithmetic.cond_subtract_3329_ v);
    f_barrett_reduce_pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        Spec.Utils.is_i16b_array_opaque 28296 (impl.f_repr v));
    f_barrett_reduce_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_barrett_reduce
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let _:Prims.unit =
          reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) Spec.Utils.is_i16b_array_opaque
        in
        Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce v);
    f_montgomery_multiply_by_constant_pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (r: i16) ->
        Spec.Utils.is_i16b 1664 r);
    f_montgomery_multiply_by_constant_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (r: i16)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr out));
    f_montgomery_multiply_by_constant
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (r: i16) ->
        let _:Prims.unit =
          reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) Spec.Utils.is_i16b_array_opaque
        in
        Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_by_constant v r);
    f_compress_1__pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        forall (i: nat).
          i < 16 ==> v (Seq.index (impl.f_repr a) i) >= 0 /\ v (Seq.index (impl.f_repr a) i) < 3329);
    f_compress_1__post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        forall (i: nat). i < 16 ==> bounded (Seq.index (impl.f_repr out) i) 1);
    f_compress_1_
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        Libcrux_ml_kem.Vector.Portable.Compress.compress_1_ a);
    f_compress_pre
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        (v v_COEFFICIENT_BITS == 4 \/ v v_COEFFICIENT_BITS == 5 \/ v v_COEFFICIENT_BITS == 10 \/
          v v_COEFFICIENT_BITS == 11) /\
        (forall (i: nat).
            i < 16 ==>
            v (Seq.index (impl.f_repr a) i) >= 0 /\ v (Seq.index (impl.f_repr a) i) < 3329));
    f_compress_post
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        (v v_COEFFICIENT_BITS == 4 \/ v v_COEFFICIENT_BITS == 5 \/ v v_COEFFICIENT_BITS == 10 \/
          v v_COEFFICIENT_BITS == 11) ==>
        (forall (i: nat). i < 16 ==> bounded (Seq.index (impl.f_repr out) i) (v v_COEFFICIENT_BITS))
    );
    f_compress
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Libcrux_ml_kem.Vector.Portable.Compress.compress v_COEFFICIENT_BITS a);
    f_decompress_ciphertext_coefficient_pre
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        (v v_COEFFICIENT_BITS == 4 \/ v v_COEFFICIENT_BITS == 5 \/ v v_COEFFICIENT_BITS == 10 \/
          v v_COEFFICIENT_BITS == 11) /\
        (forall (i: nat).
            i < 16 ==>
            v (Seq.index (impl.f_repr a) i) >= 0 /\
            v (Seq.index (impl.f_repr a) i) < pow2 (v v_COEFFICIENT_BITS)));
    f_decompress_ciphertext_coefficient_post
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_decompress_ciphertext_coefficient
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Libcrux_ml_kem.Vector.Portable.Compress.decompress_ciphertext_coefficient v_COEFFICIENT_BITS
          a);
    f_ntt_layer_1_step_pre
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
        Spec.Utils.is_i16b_array (11207 + 5 * 3328) (impl.f_repr a));
    f_ntt_layer_1_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Spec.Utils.is_i16b_array (11207 + 6 * 3328) (impl.f_repr out));
    f_ntt_layer_1_step
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        Libcrux_ml_kem.Vector.Portable.Ntt.ntt_layer_1_step a zeta0 zeta1 zeta2 zeta3);
    f_ntt_layer_2_step_pre
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        ->
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b_array (11207 + 4 * 3328) (impl.f_repr a));
    f_ntt_layer_2_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Spec.Utils.is_i16b_array (11207 + 5 * 3328) (impl.f_repr out));
    f_ntt_layer_2_step
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        ->
        Libcrux_ml_kem.Vector.Portable.Ntt.ntt_layer_2_step a zeta0 zeta1);
    f_ntt_layer_3_step_pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) ->
        Spec.Utils.is_i16b 1664 zeta /\ Spec.Utils.is_i16b_array (11207 + 3 * 3328) (impl.f_repr a));
    f_ntt_layer_3_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta: i16)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Spec.Utils.is_i16b_array (11207 + 4 * 3328) (impl.f_repr out));
    f_ntt_layer_3_step
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) ->
        Libcrux_ml_kem.Vector.Portable.Ntt.ntt_layer_3_step a zeta);
    f_inv_ntt_layer_1_step_pre
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
        Spec.Utils.is_i16b_array (4 * 3328) (impl.f_repr a));
    f_inv_ntt_layer_1_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Spec.Utils.is_i16b_array 3328 (impl.f_repr out));
    f_inv_ntt_layer_1_step
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        Libcrux_ml_kem.Vector.Portable.Ntt.inv_ntt_layer_1_step a zeta0 zeta1 zeta2 zeta3);
    f_inv_ntt_layer_2_step_pre
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        ->
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b_array 3328 (impl.f_repr a));
    f_inv_ntt_layer_2_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Spec.Utils.is_i16b_array 3328 (impl.f_repr out));
    f_inv_ntt_layer_2_step
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        ->
        Libcrux_ml_kem.Vector.Portable.Ntt.inv_ntt_layer_2_step a zeta0 zeta1);
    f_inv_ntt_layer_3_step_pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) ->
        Spec.Utils.is_i16b 1664 zeta /\ Spec.Utils.is_i16b_array 3328 (impl.f_repr a));
    f_inv_ntt_layer_3_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta: i16)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Spec.Utils.is_i16b_array 3328 (impl.f_repr out));
    f_inv_ntt_layer_3_step
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) ->
        Libcrux_ml_kem.Vector.Portable.Ntt.inv_ntt_layer_3_step a zeta);
    f_ntt_multiply_pre
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
        Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr lhs) /\
        Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr rhs));
    f_ntt_multiply_post
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr out));
    f_ntt_multiply
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        let _:Prims.unit =
          reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) Spec.Utils.is_i16b_array_opaque
        in
        Libcrux_ml_kem.Vector.Portable.Ntt.ntt_multiply lhs rhs zeta0 zeta1 zeta2 zeta3);
    f_serialize_1__pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        Spec.MLKEM.serialize_pre 1 (impl.f_repr a));
    f_serialize_1__post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Array u8 (mk_usize 2))
        ->
        Spec.MLKEM.serialize_pre 1 (impl.f_repr a) ==>
        Spec.MLKEM.serialize_post 1 (impl.f_repr a) out);
    f_serialize_1_
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> serialize_1_ a);
    f_deserialize_1__pre
    =
    (fun (a: t_Slice u8) -> (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 2);
    f_deserialize_1__post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        sz (Seq.length a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 a (impl.f_repr out));
    f_deserialize_1_ = (fun (a: t_Slice u8) -> deserialize_1_ a);
    f_serialize_4__pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        Spec.MLKEM.serialize_pre 4 (impl.f_repr a));
    f_serialize_4__post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Array u8 (mk_usize 8))
        ->
        Spec.MLKEM.serialize_pre 4 (impl.f_repr a) ==>
        Spec.MLKEM.serialize_post 4 (impl.f_repr a) out);
    f_serialize_4_
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> serialize_4_ a);
    f_deserialize_4__pre
    =
    (fun (a: t_Slice u8) -> (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 8);
    f_deserialize_4__post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        sz (Seq.length a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 a (impl.f_repr out));
    f_deserialize_4_ = (fun (a: t_Slice u8) -> deserialize_4_ a);
    f_serialize_5__pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_serialize_5__post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Array u8 (mk_usize 10))
        ->
        true);
    f_serialize_5_
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> serialize_5_ a);
    f_deserialize_5__pre
    =
    (fun (a: t_Slice u8) -> (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 10);
    f_deserialize_5__post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_deserialize_5_ = (fun (a: t_Slice u8) -> deserialize_5_ a);
    f_serialize_10__pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        Spec.MLKEM.serialize_pre 10 (impl.f_repr a));
    f_serialize_10__post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Array u8 (mk_usize 20))
        ->
        Spec.MLKEM.serialize_pre 10 (impl.f_repr a) ==>
        Spec.MLKEM.serialize_post 10 (impl.f_repr a) out);
    f_serialize_10_
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> serialize_10_ a);
    f_deserialize_10__pre
    =
    (fun (a: t_Slice u8) -> (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 20);
    f_deserialize_10__post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        sz (Seq.length a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 a (impl.f_repr out));
    f_deserialize_10_ = (fun (a: t_Slice u8) -> deserialize_10_ a);
    f_serialize_11__pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_serialize_11__post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Array u8 (mk_usize 22))
        ->
        true);
    f_serialize_11_
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> serialize_11_ a);
    f_deserialize_11__pre
    =
    (fun (a: t_Slice u8) -> (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 22);
    f_deserialize_11__post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_deserialize_11_ = (fun (a: t_Slice u8) -> deserialize_11_ a);
    f_serialize_12__pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        Spec.MLKEM.serialize_pre 12 (impl.f_repr a));
    f_serialize_12__post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Array u8 (mk_usize 24))
        ->
        Spec.MLKEM.serialize_pre 12 (impl.f_repr a) ==>
        Spec.MLKEM.serialize_post 12 (impl.f_repr a) out);
    f_serialize_12_
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> serialize_12_ a);
    f_deserialize_12__pre
    =
    (fun (a: t_Slice u8) -> (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 24);
    f_deserialize_12__post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        sz (Seq.length a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 a (impl.f_repr out));
    f_deserialize_12_ = (fun (a: t_Slice u8) -> deserialize_12_ a);
    f_rej_sample_pre
    =
    (fun (a: t_Slice u8) (out: t_Slice i16) ->
        (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 24 &&
        (Core.Slice.impl__len #i16 out <: usize) =. mk_usize 16);
    f_rej_sample_post
    =
    (fun (a: t_Slice u8) (out: t_Slice i16) (out_future, result: (t_Slice i16 & usize)) ->
        Seq.length out_future == Seq.length out /\ v result <= 16);
    f_rej_sample
    =
    fun (a: t_Slice u8) (out: t_Slice i16) ->
      let tmp0, out1:(t_Slice i16 & usize) =
        Libcrux_ml_kem.Vector.Portable.Sampling.rej_sample a out
      in
      let out:t_Slice i16 = tmp0 in
      let hax_temp_output:usize = out1 in
      out, hax_temp_output <: (t_Slice i16 & usize)
  }

#pop-options
