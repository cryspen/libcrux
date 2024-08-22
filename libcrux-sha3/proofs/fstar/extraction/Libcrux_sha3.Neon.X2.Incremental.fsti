module Libcrux_sha3.Neon.X2.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// The Keccak state for the incremental API.
type t_KeccakState = {
  f_state:Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
    Core.Core_arch.Arm_shared.Neon.t_uint64x2_t
}

/// Initialise the state and perform up to 4 absorbs at the same time,
/// using two [`KeccakState2`].
/// **PANICS** when `N` is not 2, 3, or 4.
val v__shake128_absorb_finalxN (v_N: usize) (input: t_Array (t_Array u8 (sz 34)) v_N)
    : Prims.Pure (t_Array t_KeccakState (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

/// Squeeze up to 3 x 4 (N) blocks in parallel, using two [`KeccakState2`].
/// Each block is of size `LEN`.
/// **PANICS** when `N` is not 2, 3, or 4.
val v__shake128_squeeze3xN (v_LEN v_N: usize) (state: t_Array t_KeccakState (sz 2))
    : Prims.Pure (t_Array t_KeccakState (sz 2) & t_Array (t_Array u8 v_LEN) v_N)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Squeeze up to 4 (N) blocks in parallel, using two [`KeccakState2`].
/// Each block is of size `LEN`.
/// **PANICS** when `N` is not 2, 3, or 4.
val v__shake128_squeezexN (v_LEN v_N: usize) (state: t_Array t_KeccakState (sz 2))
    : Prims.Pure (t_Array t_KeccakState (sz 2) & t_Array (t_Array u8 v_LEN) v_N)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Shake128 absorb `data0` and `data1` in the [`KeccakState`] `s`.
val shake128_absorb_final (s: t_KeccakState) (data0 data1: t_Slice u8)
    : Prims.Pure t_KeccakState Prims.l_True (fun _ -> Prims.l_True)

/// Initialise the `KeccakState2`.
val shake128_init: Prims.unit -> Prims.Pure t_KeccakState Prims.l_True (fun _ -> Prims.l_True)

/// Squeeze 2 times the first three blocks in parallel in the
/// [`KeccakState`] and return the output in `out0` and `out1`.
val shake128_squeeze_first_three_blocks (s: t_KeccakState) (out0 out1: t_Slice u8)
    : Prims.Pure (t_KeccakState & t_Slice u8 & t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// Squeeze 2 times the next block in parallel in the
/// [`KeccakState`] and return the output in `out0` and `out1`.
val shake128_squeeze_next_block (s: t_KeccakState) (out0 out1: t_Slice u8)
    : Prims.Pure (t_KeccakState & t_Slice u8 & t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
