module Libcrux_ml_kem.Vector.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

type t_PortableVector = { f_elements:t_Array i16 (sz 16) }

val from_i16_array (array: t_Slice i16)
    : Prims.Pure t_PortableVector
      (requires (Core.Slice.impl__len #i16 array <: usize) =. sz 16)
      (ensures
        fun result ->
          let result:t_PortableVector = result in
          result.f_elements == array)

val to_i16_array (x: t_PortableVector)
    : Prims.Pure (t_Array i16 (sz 16))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array i16 (sz 16) = result in
          result == x.f_elements)

val zero: Prims.unit
  -> Prims.Pure t_PortableVector
      Prims.l_True
      (ensures
        fun result ->
          let result:t_PortableVector = result in
          result.f_elements == Seq.create 16 (mk_i16 0))
