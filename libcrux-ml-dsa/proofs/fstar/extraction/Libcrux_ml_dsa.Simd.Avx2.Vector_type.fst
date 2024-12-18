module Libcrux_ml_dsa.Simd.Avx2.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From t_AVX2SIMDUnit Libcrux_intrinsics.Avx2_extract.t_Vec256 =
  {
    f_from_pre = (fun (coefficients: Libcrux_intrinsics.Avx2_extract.t_Vec256) -> true);
    f_from_post
    =
    (fun (coefficients: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_AVX2SIMDUnit) -> true);
    f_from
    =
    fun (coefficients: Libcrux_intrinsics.Avx2_extract.t_Vec256) ->
      { f_coefficients = coefficients } <: t_AVX2SIMDUnit
  }

let v_ZERO (_: Prims.unit) =
  Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
    #t_AVX2SIMDUnit
    #FStar.Tactics.Typeclasses.solve
    (Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 ()
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

let from_coefficient_array (coefficient_array: t_Slice i32) =
  Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
    #t_AVX2SIMDUnit
    #FStar.Tactics.Typeclasses.solve
    (Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_i32 coefficient_array
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Clone.t_Clone t_AVX2SIMDUnit

let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Marker.t_Copy t_AVX2SIMDUnit

let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Clone.t_Clone t_AVX2SIMDUnit

let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Marker.t_Copy t_AVX2SIMDUnit

let impl_2 = impl_2'

let to_coefficient_array (x: t_AVX2SIMDUnit) =
  let coefficient_array:t_Array i32 (sz 8) = Rust_primitives.Hax.repeat 0l (sz 8) in
  let coefficient_array:t_Array i32 (sz 8) =
    Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_i32 coefficient_array x.f_coefficients
  in
  coefficient_array
