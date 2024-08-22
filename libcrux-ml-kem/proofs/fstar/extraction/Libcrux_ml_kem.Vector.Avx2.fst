module Libcrux_ml_kem.Vector.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let from_i16_array (array: t_Slice i16) =
  { f_elements = Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_i16 array } <: t_SIMD256Vector

let to_i16_array (v: t_SIMD256Vector) =
  let output:t_Array i16 (sz 16) = Rust_primitives.Hax.repeat 0s (sz 16) in
  let output:t_Array i16 (sz 16) =
    Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_i16 output v.f_elements
  in
  output

let zero (_: Prims.unit) =
  { f_elements = Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 () } <: t_SIMD256Vector
