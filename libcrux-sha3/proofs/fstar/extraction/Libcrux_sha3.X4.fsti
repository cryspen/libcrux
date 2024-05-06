module Libcrux_sha3.X4
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Incremental state
val t_Shake128StateX4:Type

/// Absorb 4 blocks.
/// A blocks MUST all be the same length.
/// Each slice MUST be a multiple of the block length 168.
val impl__Shake128StateX4__absorb_4blocks
      (self: t_Shake128StateX4)
      (input: t_Array (t_Slice u8) (sz 4))
    : Prims.Pure t_Shake128StateX4 Prims.l_True (fun _ -> Prims.l_True)

/// Absorb up to 4 blocks.
/// The `input` must be of length 1 to 4.
/// A blocks MUST all be the same length.
/// Each slice MUST be a multiple of the block length 168.
val impl__Shake128StateX4__absorb_final
      (v_N: usize)
      (self: t_Shake128StateX4)
      (input: t_Array (t_Slice u8) v_N)
    : Prims.Pure t_Shake128StateX4 Prims.l_True (fun _ -> Prims.l_True)

/// This is only used internally to work around Eurydice bugs.
val impl__Shake128StateX4__free_memory (self: t_Shake128StateX4)
    : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

/// Create a new Shake128 x4 state.
val impl__Shake128StateX4__new: Prims.unit
  -> Prims.Pure t_Shake128StateX4 Prims.l_True (fun _ -> Prims.l_True)

/// Squeeze `M` blocks of length `N`
val impl__Shake128StateX4__squeeze_blocks (v_N v_M: usize) (self: t_Shake128StateX4)
    : Prims.Pure (t_Shake128StateX4 & t_Array (t_Array u8 v_N) v_M)
      Prims.l_True
      (fun _ -> Prims.l_True)
