module Libcrux_ml_kem.Vector.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

noeq

type t_SIMD256Vector = { f_elements:Libcrux_intrinsics.Avx2_extract.t_Vec256 }

let repr (x:t_SIMD256Vector) : t_Array i16 (sz 16) = Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 x.f_elements

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Clone.t_Clone t_SIMD256Vector

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Marker.t_Copy t_SIMD256Vector

val vec_zero: Prims.unit
  -> Prims.Pure t_SIMD256Vector
      Prims.l_True
      (ensures
        fun result ->
          let result:t_SIMD256Vector = result in
          repr result == Seq.create 16 (mk_i16 0))

val vec_to_i16_array (v: t_SIMD256Vector)
    : Prims.Pure (t_Array i16 (sz 16))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array i16 (sz 16) = result in
          result == repr v)

val vec_from_i16_array (array: t_Slice i16)
    : Prims.Pure t_SIMD256Vector
      Prims.l_True
      (ensures
        fun result ->
          let result:t_SIMD256Vector = result in
          repr result == array)

val cond_subtract_3329_ (vector: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector
      (requires Spec.Utils.is_i16b_array (pow2 12 - 1) (repr vector))
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          repr out ==
          Spec.Utils.map_array (fun x -> if x >=. (mk_i16 3329) then x -! (mk_i16 3329) else x)
            (repr vector))

val compress_1_ (vector: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector
      (requires
        forall (i: nat).
          i < 16 ==> v (Seq.index (repr vector) i) >= 0 /\ v (Seq.index (repr vector) i) < 3329)
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          forall (i: nat). i < 16 ==> bounded (Seq.index (repr out) i) 1)

val compress (v_COEFFICIENT_BITS: i32) (vector: t_SIMD256Vector)
    : Prims.Pure t_SIMD256Vector
      (requires
        (v v_COEFFICIENT_BITS == 4 \/ v v_COEFFICIENT_BITS == 5 \/ v v_COEFFICIENT_BITS == 10 \/
          v v_COEFFICIENT_BITS == 11) /\
        (forall (i: nat).
            i < 16 ==> v (Seq.index (repr vector) i) >= 0 /\ v (Seq.index (repr vector) i) < 3329))
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          (v v_COEFFICIENT_BITS == 4 \/ v v_COEFFICIENT_BITS == 5 \/ v v_COEFFICIENT_BITS == 10 \/
            v v_COEFFICIENT_BITS == 11) ==>
          (forall (i: nat). i < 16 ==> bounded (Seq.index (repr out) i) (v v_COEFFICIENT_BITS)))

val ntt_layer_1_step (vector: t_SIMD256Vector) (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure t_SIMD256Vector
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
        Spec.Utils.is_i16b_array (11207 + 5 * 3328) (repr vector))
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          Spec.Utils.is_i16b_array (11207 + 6 * 3328) (repr out))

val ntt_layer_2_step (vector: t_SIMD256Vector) (zeta0 zeta1: i16)
    : Prims.Pure t_SIMD256Vector
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b_array (11207 + 4 * 3328) (repr vector))
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          Spec.Utils.is_i16b_array (11207 + 5 * 3328) (repr out))

val ntt_layer_3_step (vector: t_SIMD256Vector) (zeta: i16)
    : Prims.Pure t_SIMD256Vector
      (requires
        Spec.Utils.is_i16b 1664 zeta /\ Spec.Utils.is_i16b_array (11207 + 3 * 3328) (repr vector))
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          Spec.Utils.is_i16b_array (11207 + 4 * 3328) (repr out))

val inv_ntt_layer_1_step (vector: t_SIMD256Vector) (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure t_SIMD256Vector
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
        Spec.Utils.is_i16b_array (4 * 3328) (repr vector))
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          Spec.Utils.is_i16b_array 3328 (repr out))

val inv_ntt_layer_2_step (vector: t_SIMD256Vector) (zeta0 zeta1: i16)
    : Prims.Pure t_SIMD256Vector
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b_array 3328 (repr vector))
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          Spec.Utils.is_i16b_array 3328 (repr out))

val inv_ntt_layer_3_step (vector: t_SIMD256Vector) (zeta: i16)
    : Prims.Pure t_SIMD256Vector
      (requires Spec.Utils.is_i16b 1664 zeta /\ Spec.Utils.is_i16b_array 3328 (repr vector))
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          Spec.Utils.is_i16b_array 3328 (repr out))

val ntt_multiply (lhs rhs: t_SIMD256Vector) (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure t_SIMD256Vector
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
        Spec.Utils.is_i16b_array 3328 (repr lhs) /\ Spec.Utils.is_i16b_array 3328 (repr rhs))
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          Spec.Utils.is_i16b_array 3328 (repr out))

val serialize_1_ (vector: t_SIMD256Vector)
    : Prims.Pure (t_Array u8 (sz 2))
      (requires Spec.MLKEM.serialize_pre 1 (repr vector))
      (ensures
        fun out ->
          let out:t_Array u8 (sz 2) = out in
          Spec.MLKEM.serialize_pre 1 (repr vector) ==> Spec.MLKEM.serialize_post 1 (repr vector) out
      )

val deserialize_1_ (bytes: t_Slice u8)
    : Prims.Pure t_SIMD256Vector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. sz 2)
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          sz (Seq.length bytes) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 bytes (repr out))

val serialize_4_ (vector: t_SIMD256Vector)
    : Prims.Pure (t_Array u8 (sz 8))
      (requires Spec.MLKEM.serialize_pre 4 (repr vector))
      (ensures
        fun out ->
          let out:t_Array u8 (sz 8) = out in
          Spec.MLKEM.serialize_pre 4 (repr vector) ==> Spec.MLKEM.serialize_post 4 (repr vector) out
      )

val deserialize_4_ (bytes: t_Slice u8)
    : Prims.Pure t_SIMD256Vector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. sz 8)
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          sz (Seq.length bytes) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 bytes (repr out))

val serialize_10_ (vector: t_SIMD256Vector)
    : Prims.Pure (t_Array u8 (sz 20))
      (requires Spec.MLKEM.serialize_pre 10 (repr vector))
      (ensures
        fun out ->
          let out:t_Array u8 (sz 20) = out in
          Spec.MLKEM.serialize_pre 10 (repr vector) ==>
          Spec.MLKEM.serialize_post 10 (repr vector) out)

val deserialize_10_ (bytes: t_Slice u8)
    : Prims.Pure t_SIMD256Vector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. sz 20)
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          sz (Seq.length bytes) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 bytes (repr out))

val serialize_12_ (vector: t_SIMD256Vector)
    : Prims.Pure (t_Array u8 (sz 24))
      (requires Spec.MLKEM.serialize_pre 12 (repr vector))
      (ensures
        fun out ->
          let out:t_Array u8 (sz 24) = out in
          Spec.MLKEM.serialize_pre 12 (repr vector) ==>
          Spec.MLKEM.serialize_post 12 (repr vector) out)

val deserialize_12_ (bytes: t_Slice u8)
    : Prims.Pure t_SIMD256Vector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. sz 24)
      (ensures
        fun out ->
          let out:t_SIMD256Vector = out in
          sz (Seq.length bytes) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 bytes (repr out))

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_ml_kem.Vector.Traits.t_Repr t_SIMD256Vector

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3:Libcrux_ml_kem.Vector.Traits.t_Operations t_SIMD256Vector
