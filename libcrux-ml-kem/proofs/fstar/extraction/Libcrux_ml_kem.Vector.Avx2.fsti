module Libcrux_ml_kem.Vector.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_SIMD256Vector = { f_elements:u8 }

val zero: Prims.unit -> Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

val to_i16_array (v: t_SIMD256Vector)
    : Prims.Pure (t_Array i16 (sz 16)) Prims.l_True (fun _ -> Prims.l_True)

val from_i16_array (array: t_Slice i16)
    : Prims.Pure t_SIMD256Vector Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_ml_kem.Vector.Traits.t_Operations t_SIMD256Vector
