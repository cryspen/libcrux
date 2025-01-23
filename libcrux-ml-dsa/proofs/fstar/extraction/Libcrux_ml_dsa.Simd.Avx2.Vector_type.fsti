module Libcrux_ml_dsa.Simd.Avx2.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// The vector type
type t_Vec256 = { f_value:Libcrux_intrinsics.Avx2_extract.t_Vec256 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core.Clone.t_Clone t_Vec256

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Marker.t_Copy t_Vec256

/// Create an all-zero vector coefficient
val zero: Prims.unit -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

/// Create a coefficient from an `i32` array
val from_coefficient_array (coefficient_array: t_Slice i32) (out: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

/// Write out the coefficient to an `i32` array
val to_coefficient_array (value: t_Vec256) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32) Prims.l_True (fun _ -> Prims.l_True)
