module Libcrux_ml_dsa.Simd.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

type t_Coefficients = { f_values:t_Array i32 (sz 8) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core.Clone.t_Clone t_Coefficients

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Marker.t_Copy t_Coefficients

val zero: Prims.unit -> Prims.Pure t_Coefficients Prims.l_True (fun _ -> Prims.l_True)

val from_coefficient_array (array: t_Slice i32) (out: t_Coefficients)
    : Prims.Pure t_Coefficients Prims.l_True (fun _ -> Prims.l_True)

val to_coefficient_array (value: t_Coefficients) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32) Prims.l_True (fun _ -> Prims.l_True)
