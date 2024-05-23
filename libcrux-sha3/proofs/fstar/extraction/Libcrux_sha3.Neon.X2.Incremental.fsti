module Libcrux_sha3.Neon.X2.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_KeccakState2 =
  Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2) Core.Core_arch.Arm_shared.Neon.t_uint64x2_t

val shake128_absorb_final
      (s:
          Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
            Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
      (data0 data1: t_Slice u8)
    : Prims.Pure
      (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2) Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Initialise the state and perform up to 4 absorbs at the same time,
/// using two [`KeccakState2`].
/// **PANICS** when `N` is not 2, 3, or 4.
val shake128_absorb_finalxN (v_N: usize) (input: t_Array (t_Array u8 (sz 34)) v_N)
    : Prims.Pure
      (t_Array
          (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
              Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) (sz 2))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Initialise the `KeccakState2`.
val shake128_init: Prims.unit
  -> Prims.Pure
      (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2) Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Squeeze up to 3 x 4 (N) blocks in parallel, using two [`KeccakState2`].
/// Each block is of size `LEN`.
/// **PANICS** when `N` is not 2, 3, or 4.
val shake128_squeeze3xN
      (v_LEN v_N: usize)
      (state:
          t_Array
            (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
                Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) (sz 2))
    : Prims.Pure
      (t_Array
          (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
              Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) (sz 2) &
        t_Array (t_Array u8 v_LEN) v_N) Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_first_three_blocks
      (s:
          Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
            Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
      (out0 out1: t_Slice u8)
    : Prims.Pure
      (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2) Core.Core_arch.Arm_shared.Neon.t_uint64x2_t &
        t_Slice u8 &
        t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_next_block
      (s:
          Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
            Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
      (out0 out1: t_Slice u8)
    : Prims.Pure
      (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2) Core.Core_arch.Arm_shared.Neon.t_uint64x2_t &
        t_Slice u8 &
        t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// Squeeze up to 4 (N) blocks in parallel, using two [`KeccakState2`].
/// Each block is of size `LEN`.
/// **PANICS** when `N` is not 2, 3, or 4.
val shake128_squeezexN
      (v_LEN v_N: usize)
      (state:
          t_Array
            (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
                Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) (sz 2))
    : Prims.Pure
      (t_Array
          (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
              Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) (sz 2) &
        t_Array (t_Array u8 v_LEN) v_N) Prims.l_True (fun _ -> Prims.l_True)
