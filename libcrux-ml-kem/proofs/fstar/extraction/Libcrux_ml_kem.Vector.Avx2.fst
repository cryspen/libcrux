module Libcrux_ml_kem.Vector.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let from_i16_array (array: t_Slice i16) =
  let result:t_SIMD256Vector =
    { f_elements = Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_i16 array } <: t_SIMD256Vector
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let to_i16_array (v: t_SIMD256Vector) =
  let output:t_Array i16 (sz 16) = Rust_primitives.Hax.repeat 0s (sz 16) in
  let output:t_Array i16 (sz 16) =
    Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_i16 output v.f_elements
  in
  let result:t_Array i16 (sz 16) = output in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let zero (_: Prims.unit) =
  let result:t_SIMD256Vector =
    { f_elements = Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 () } <: t_SIMD256Vector
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result
