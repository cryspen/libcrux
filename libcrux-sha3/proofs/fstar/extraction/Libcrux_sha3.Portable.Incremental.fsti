module Libcrux_sha3.Portable.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Absorb
val shake128_absorb_final
      (s: Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64)
      (data0: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Initialise the SHAKE state.
val shake128_init: Prims.unit
  -> Prims.Pure (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Squeeze three blocks
val shake128_squeeze_first_three_blocks
      (s: Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64)
      (out0: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64 & t_Slice u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Squeeze another block
val shake128_squeeze_next_block
      (s: Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64)
      (out0: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64 & t_Slice u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
