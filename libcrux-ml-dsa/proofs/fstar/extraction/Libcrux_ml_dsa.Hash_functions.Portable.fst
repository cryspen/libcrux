module Libcrux_ml_dsa.Hash_functions.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let init_absorb__init_absorb (input: t_Slice u8) =
  let state:Libcrux_sha3.Portable.t_KeccakState =
    Libcrux_sha3.Portable.Incremental.shake128_init ()
  in
  let state:Libcrux_sha3.Portable.t_KeccakState =
    Libcrux_sha3.Portable.Incremental.shake128_absorb_final state input
  in
  state
