module Libcrux_ml_dsa.Simd.Avx2.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

type t_AVX2SIMDUnit = { f_coefficients:u8 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core.Convert.t_From t_AVX2SIMDUnit u8

val v_ZERO: Prims.unit -> Prims.Pure t_AVX2SIMDUnit Prims.l_True (fun _ -> Prims.l_True)

val from_coefficient_array (coefficient_array: t_Slice i32)
    : Prims.Pure t_AVX2SIMDUnit Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Clone.t_Clone t_AVX2SIMDUnit

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Marker.t_Copy t_AVX2SIMDUnit

val to_coefficient_array (x: t_AVX2SIMDUnit)
    : Prims.Pure (t_Array i32 (sz 8)) Prims.l_True (fun _ -> Prims.l_True)
