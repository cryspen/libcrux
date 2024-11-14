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

val vec_from_i16_array (array: t_Slice i16)
    : Prims.Pure t_SIMD256Vector
      Prims.l_True
      (ensures
        fun result ->
          let result:t_SIMD256Vector = result in
          repr result == array)

val vec_zero: Prims.unit
  -> Prims.Pure t_SIMD256Vector
      Prims.l_True
      (ensures
        fun result ->
          let result:t_SIMD256Vector = result in
          repr result == Seq.create 16 0s)

val vec_to_i16_array (v: t_SIMD256Vector)
    : Prims.Pure (t_Array i16 (sz 16))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array i16 (sz 16) = result in
          result == repr v)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_ml_kem.Vector.Traits.t_Repr t_SIMD256Vector

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3:Libcrux_ml_kem.Vector.Traits.t_Operations t_SIMD256Vector
