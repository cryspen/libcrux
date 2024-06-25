module Libcrux_sha3.Avx2.X4.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_KeccakState4 = { f_state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 (sz 2) }

val shake128_absorb_final (s: t_KeccakState4) (data0 data1 data2 data3: t_Slice u8)
    : Prims.Pure t_KeccakState4 Prims.l_True (fun _ -> Prims.l_True)

/// Initialise the [`KeccakState4`].
val shake128_init: Prims.unit -> Prims.Pure t_KeccakState4 Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_first_three_blocks
      (s: t_KeccakState4)
      (out: t_Array (t_Array u8 (sz 504)) (sz 4))
    : Prims.Pure (t_KeccakState4 & t_Array (t_Array u8 (sz 504)) (sz 4))
      Prims.l_True
      (fun _ -> Prims.l_True)

val shake128_squeeze_next_block (s: t_KeccakState4) (out: t_Array (t_Array u8 (sz 168)) (sz 4))
    : Prims.Pure (t_KeccakState4 & t_Array (t_Array u8 (sz 168)) (sz 4))
      Prims.l_True
      (fun _ -> Prims.l_True)
