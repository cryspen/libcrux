module Libcrux_ml_dsa.Hash_functions.Simd256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// AVX2 SHAKE 128 state
/// This only implements the XofX4 API. For the single Xof, the portable
/// version is used.
val t_Shake128x4:Type0

/// AVX2 SHAKE 256 x4 state.
val t_Shake256x4:Type0

/// AVX2 SHAKE 256 state
val t_Shake256:Type0

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 t_Shake128x4

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof t_Shake256

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 t_Shake256x4

/// Init the state and absorb 4 blocks in parallel.
val init_absorb (input0 input1 input2 input3: t_Slice u8)
    : Prims.Pure t_Shake128x4 Prims.l_True (fun _ -> Prims.l_True)

val init_absorb_final_shake256 (input: t_Slice u8)
    : Prims.Pure t_Shake256 Prims.l_True (fun _ -> Prims.l_True)

val init_absorb_x4 (input0 input1 input2 input3: t_Slice u8)
    : Prims.Pure t_Shake256x4 Prims.l_True (fun _ -> Prims.l_True)

val shake256 (v_OUTPUT_LENGTH: usize) (input: t_Slice u8) (out: t_Array u8 v_OUTPUT_LENGTH)
    : Prims.Pure (t_Array u8 v_OUTPUT_LENGTH) Prims.l_True (fun _ -> Prims.l_True)

val shake256_x4
      (v_OUT_LEN: usize)
      (input0 input1 input2 input3: t_Slice u8)
      (out0 out1 out2 out3: t_Array u8 v_OUT_LEN)
    : Prims.Pure
      (t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN)
      Prims.l_True
      (fun _ -> Prims.l_True)

val squeeze_first_block_shake256 (state: t_Shake256)
    : Prims.Pure (t_Shake256 & t_Array u8 (sz 136)) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_first_block_x4 (state: t_Shake256x4)
    : Prims.Pure
      (t_Shake256x4 &
        (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
      Prims.l_True
      (fun _ -> Prims.l_True)

val squeeze_first_five_blocks (state: t_Shake128x4) (out0 out1 out2 out3: t_Array u8 (sz 840))
    : Prims.Pure
      (t_Shake128x4 & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
        t_Array u8 (sz 840)) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_next_block (state: t_Shake128x4)
    : Prims.Pure
      (t_Shake128x4 &
        (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168)))
      Prims.l_True
      (fun _ -> Prims.l_True)

val squeeze_next_block_shake256 (state: t_Shake256)
    : Prims.Pure (t_Shake256 & t_Array u8 (sz 136)) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_next_block_x4 (state: t_Shake256x4)
    : Prims.Pure
      (t_Shake256x4 &
        (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
      Prims.l_True
      (fun _ -> Prims.l_True)
