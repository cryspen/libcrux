module Libcrux_sha3.Generic_keccak
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Traits in
  ()

type t_KeccakState (v_N: usize) (v_T: Type0) {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
  = { f_st:t_Array (t_Array v_T (sz 5)) (sz 5) }
