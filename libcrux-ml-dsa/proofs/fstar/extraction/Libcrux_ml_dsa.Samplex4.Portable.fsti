module Libcrux_ml_dsa.Samplex4.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Portable in
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

type t_PortableSampler = | PortableSampler : t_PortableSampler

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_ml_dsa.Samplex4.t_X4Sampler t_PortableSampler
