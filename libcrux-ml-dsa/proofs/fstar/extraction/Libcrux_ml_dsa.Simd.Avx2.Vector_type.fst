module Libcrux_ml_dsa.Simd.Avx2.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

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

let to_coefficient_array (x: t_AVX2SIMDUnit) =
  let coefficient_array:t_Array i32 (sz 8) = Rust_primitives.Hax.repeat 0l (sz 8) in
  let coefficient_array:t_Array i32 (sz 8) =
    Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_i32 coefficient_array x.f_coefficients
  in
  coefficient_array
