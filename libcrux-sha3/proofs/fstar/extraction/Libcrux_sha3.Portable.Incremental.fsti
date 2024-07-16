module Libcrux_sha3.Portable.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Absorb
val shake128_absorb_final (s: Libcrux_sha3.Portable.t_KeccakState) (data0: t_Slice u8)
    : Prims.Pure Libcrux_sha3.Portable.t_KeccakState Prims.l_True (fun _ -> Prims.l_True)

/// Create a new SHAKE-128 state object.
val shake128_init: Prims.unit
  -> Prims.Pure Libcrux_sha3.Portable.t_KeccakState Prims.l_True (fun _ -> Prims.l_True)

/// Squeeze five blocks
val shake128_squeeze_first_five_blocks (s: Libcrux_sha3.Portable.t_KeccakState) (out0: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Portable.t_KeccakState & t_Slice u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Squeeze three blocks
val shake128_squeeze_first_three_blocks (s: Libcrux_sha3.Portable.t_KeccakState) (out0: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Portable.t_KeccakState & t_Slice u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Squeeze another block
val shake128_squeeze_next_block (s: Libcrux_sha3.Portable.t_KeccakState) (out0: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Portable.t_KeccakState & t_Slice u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Absorb some data for SHAKE-256 for the last time
val shake256_absorb_final (s: Libcrux_sha3.Portable.t_KeccakState) (data0: t_Slice u8)
    : Prims.Pure Libcrux_sha3.Portable.t_KeccakState Prims.l_True (fun _ -> Prims.l_True)

/// Create a new SHAKE-256 state object.
val shake256_init: Prims.unit
  -> Prims.Pure Libcrux_sha3.Portable.t_KeccakState Prims.l_True (fun _ -> Prims.l_True)

/// Squeeze the first SHAKE-256 block
val shake256_squeeze_first_block (s: Libcrux_sha3.Portable.t_KeccakState) (out0: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Portable.t_KeccakState & t_Slice u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Squeeze the next SHAKE-256 block
val shake256_squeeze_next_block (s: Libcrux_sha3.Portable.t_KeccakState) (out0: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Portable.t_KeccakState & t_Slice u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
