module Libcrux_ml_dsa.Simd.Avx2.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let from_coefficient_array
      (coefficient_array: t_Slice i32)
      (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
     =
  let hax_temp_output, out:(Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256) =
    (), Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_i32 coefficient_array
    <:
    (Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  out

let to_coefficient_array (value: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice i32) =
  let out:t_Slice i32 = Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_i32 out value in
  out

let zero (_: Prims.unit) = Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_AVX2SIMDUnit

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_AVX2SIMDUnit

let impl_1 = impl_1'
