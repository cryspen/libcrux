module Libcrux_sha3.Neon.X2.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Simd.Arm64 in
  let open Libcrux_sha3.Traits in
  ()

unfold
let t_KeccakState2Internal = Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2) u8

type t_KeccakState2 = { f_state:Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2) u8 }

val shake128_absorb_final (s: t_KeccakState2) (data0 data1: t_Slice u8)
    : Prims.Pure t_KeccakState2 Prims.l_True (fun _ -> Prims.l_True)

/// Initialise the `KeccakState2`.
val shake128_init: Prims.unit -> Prims.Pure t_KeccakState2 Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_first_three_blocks
      (s: t_KeccakState2)
      (out: t_Array (t_Array u8 (sz 504)) (sz 2))
    : Prims.Pure (t_KeccakState2 & t_Array (t_Array u8 (sz 504)) (sz 2))
      Prims.l_True
      (fun _ -> Prims.l_True)

val shake128_squeeze_next_block (s: t_KeccakState2) (out: t_Array (t_Array u8 (sz 168)) (sz 2))
    : Prims.Pure (t_KeccakState2 & t_Array (t_Array u8 (sz 168)) (sz 2))
      Prims.l_True
      (fun _ -> Prims.l_True)
