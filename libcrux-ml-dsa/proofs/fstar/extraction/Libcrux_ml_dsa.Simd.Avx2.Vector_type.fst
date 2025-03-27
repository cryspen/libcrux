module Libcrux_ml_dsa.Simd.Avx2.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

/// The vector type
type t_Vec256 = { f_value:Minicore.Core_arch.X86.t_e_ee_m256i }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_Vec256

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_Vec256

let impl_1 = impl_1'

/// Create an all-zero vector coefficient
let zero (_: Prims.unit) : t_Vec256 =
  { f_value = Libcrux_intrinsics.Avx2.mm256_setzero_si256 () } <: t_Vec256

/// Create a coefficient from an `i32` array
let from_coefficient_array (coefficient_array: t_Slice i32) (out: t_Vec256) : t_Vec256 =
  let out:t_Vec256 =
    { out with f_value = Libcrux_intrinsics.Avx2.mm256_loadu_si256_i32 coefficient_array }
    <:
    t_Vec256
  in
  out

/// Write out the coefficient to an `i32` array
let to_coefficient_array (value: t_Vec256) (out: t_Slice i32) : t_Slice i32 =
  let out:t_Slice i32 = Libcrux_intrinsics.Avx2.mm256_storeu_si256_i32 out value.f_value in
  out
