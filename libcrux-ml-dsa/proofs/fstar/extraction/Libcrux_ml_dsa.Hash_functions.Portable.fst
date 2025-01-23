module Libcrux_ml_dsa.Hash_functions.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

assume
val t_Shake128': eqtype

let t_Shake128 = t_Shake128'

assume
val t_Shake128X4': eqtype

let t_Shake128X4 = t_Shake128X4'

assume
val t_Shake256': eqtype

let t_Shake256 = t_Shake256'

assume
val t_Shake256X4': eqtype

let t_Shake256X4 = t_Shake256X4'

assume
val t_Shake256Xof': eqtype

let t_Shake256Xof = t_Shake256Xof'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 t_Shake128X4

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof t_Shake128

let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof t_Shake256

let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 t_Shake256X4

let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof t_Shake256Xof

let impl_4 = impl_4'

assume
val init_absorb':
    input0: t_Slice u8 ->
    input1: t_Slice u8 ->
    input2: t_Slice u8 ->
    input3: t_Slice u8
  -> Prims.Pure t_Shake128X4 Prims.l_True (fun _ -> Prims.l_True)

let init_absorb = init_absorb'

assume
val init_absorb_final_shake256': input: t_Slice u8
  -> Prims.Pure t_Shake256 Prims.l_True (fun _ -> Prims.l_True)

let init_absorb_final_shake256 = init_absorb_final_shake256'

assume
val init_absorb_x4':
    input0: t_Slice u8 ->
    input1: t_Slice u8 ->
    input2: t_Slice u8 ->
    input3: t_Slice u8
  -> Prims.Pure t_Shake256X4 Prims.l_True (fun _ -> Prims.l_True)

let init_absorb_x4 = init_absorb_x4'

assume
val shake128': input: t_Slice u8 -> out: t_Slice u8
  -> Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let shake128 = shake128'

assume
val shake256': v_OUTPUT_LENGTH: usize -> input: t_Slice u8 -> out: t_Array u8 v_OUTPUT_LENGTH
  -> Prims.Pure (t_Array u8 v_OUTPUT_LENGTH) Prims.l_True (fun _ -> Prims.l_True)

let shake256 (v_OUTPUT_LENGTH: usize) = shake256' v_OUTPUT_LENGTH

assume
val squeeze_first_block_shake256': state: t_Shake256
  -> Prims.Pure (t_Shake256 & t_Array u8 (mk_usize 136)) Prims.l_True (fun _ -> Prims.l_True)

let squeeze_first_block_shake256 = squeeze_first_block_shake256'

assume
val squeeze_first_block_x4': state: t_Shake256X4
  -> Prims.Pure
      (t_Shake256X4 &
        (t_Array u8 (mk_usize 136) & t_Array u8 (mk_usize 136) & t_Array u8 (mk_usize 136) &
          t_Array u8 (mk_usize 136))) Prims.l_True (fun _ -> Prims.l_True)

let squeeze_first_block_x4 = squeeze_first_block_x4'

assume
val squeeze_first_five_blocks':
    state: t_Shake128X4 ->
    out0: t_Array u8 (mk_usize 840) ->
    out1: t_Array u8 (mk_usize 840) ->
    out2: t_Array u8 (mk_usize 840) ->
    out3: t_Array u8 (mk_usize 840)
  -> Prims.Pure
      (t_Shake128X4 & t_Array u8 (mk_usize 840) & t_Array u8 (mk_usize 840) &
        t_Array u8 (mk_usize 840) &
        t_Array u8 (mk_usize 840)) Prims.l_True (fun _ -> Prims.l_True)

let squeeze_first_five_blocks = squeeze_first_five_blocks'

assume
val squeeze_next_block': state: t_Shake128X4
  -> Prims.Pure
      (t_Shake128X4 &
        (t_Array u8 (mk_usize 168) & t_Array u8 (mk_usize 168) & t_Array u8 (mk_usize 168) &
          t_Array u8 (mk_usize 168))) Prims.l_True (fun _ -> Prims.l_True)

let squeeze_next_block = squeeze_next_block'

assume
val squeeze_next_block_shake256': state: t_Shake256
  -> Prims.Pure (t_Shake256 & t_Array u8 (mk_usize 136)) Prims.l_True (fun _ -> Prims.l_True)

let squeeze_next_block_shake256 = squeeze_next_block_shake256'

assume
val squeeze_next_block_x4': state: t_Shake256X4
  -> Prims.Pure
      (t_Shake256X4 &
        (t_Array u8 (mk_usize 136) & t_Array u8 (mk_usize 136) & t_Array u8 (mk_usize 136) &
          t_Array u8 (mk_usize 136))) Prims.l_True (fun _ -> Prims.l_True)

let squeeze_next_block_x4 = squeeze_next_block_x4'
