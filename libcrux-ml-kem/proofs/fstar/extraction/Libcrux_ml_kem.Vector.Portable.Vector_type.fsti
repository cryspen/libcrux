module Libcrux_ml_kem.Vector.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

type t_PortableVector = { f_elements:t_Array i16 (mk_usize 16) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core.Clone.t_Clone t_PortableVector

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Marker.t_Copy t_PortableVector

val zero: Prims.unit
  -> Prims.Pure t_PortableVector
      Prims.l_True
      (ensures
        fun result ->
          let result:t_PortableVector = result in
          result.f_elements == Seq.create 16 (mk_i16 0))

val to_i16_array (x: t_PortableVector)
    : Prims.Pure (t_Array i16 (mk_usize 16))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array i16 (mk_usize 16) = result in
          result == x.f_elements)

val from_i16_array (array: t_Slice i16)
    : Prims.Pure t_PortableVector
      (requires (Core.Slice.impl__len #i16 array <: usize) =. mk_usize 16)
      (ensures
        fun result ->
          let result:t_PortableVector = result in
          result.f_elements == array)
