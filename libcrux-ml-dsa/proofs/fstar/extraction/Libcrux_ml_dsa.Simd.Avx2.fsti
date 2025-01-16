module Libcrux_ml_dsa.Simd.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Avx2.Vector_type in
  ()

/// Implementing the [`Operations`] for AVX2.
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_ml_dsa.Simd.Traits.t_Operations Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
