module Libcrux_ml_dsa.Hash_functions.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// Portable SHAKE 128 state
type t_Shake128 = | Shake128 : t_Shake128

/// Portable SHAKE 128 x4 state.
/// We\'re using a portable implementation so this is actually sequential.
val t_Shake128X4:Type0

/// Portable SHAKE 256 state
val t_Shake256:Type0

/// Portable SHAKE 256 x4 state.
/// We\'re using a portable implementation so this is actually sequential.
val t_Shake256X4:Type0

val t_Shake256Absorb:Type0

val t_Shake256Squeeze:Type0

val init_absorb__init_absorb (input: t_Slice u8)
    : Prims.Pure Libcrux_sha3.Portable.t_KeccakState Prims.l_True (fun _ -> Prims.l_True)

val init_absorb (input0 input1 input2 input3: t_Slice u8)
    : Prims.Pure t_Shake128X4 Prims.l_True (fun _ -> Prims.l_True)

val init_absorb_shake256 (input: t_Slice u8)
    : Prims.Pure t_Shake256 Prims.l_True (fun _ -> Prims.l_True)

val init_absorb_x4 (input0 input1 input2 input3: t_Slice u8)
    : Prims.Pure t_Shake256X4 Prims.l_True (fun _ -> Prims.l_True)

val shake128 (v_OUTPUT_LENGTH: usize) (input: t_Slice u8) (out: t_Array u8 v_OUTPUT_LENGTH)
    : Prims.Pure (t_Array u8 v_OUTPUT_LENGTH) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof t_Shake128 =
  {
    f_shake128_pre
    =
    (fun (v_OUTPUT_LENGTH: usize) (input: t_Slice u8) (out: t_Array u8 v_OUTPUT_LENGTH) -> true);
    f_shake128_post
    =
    (fun
        (v_OUTPUT_LENGTH: usize)
        (input: t_Slice u8)
        (out: t_Array u8 v_OUTPUT_LENGTH)
        (out1: t_Array u8 v_OUTPUT_LENGTH)
        ->
        true);
    f_shake128
    =
    fun (v_OUTPUT_LENGTH: usize) (input: t_Slice u8) (out: t_Array u8 v_OUTPUT_LENGTH) ->
      let out:t_Array u8 v_OUTPUT_LENGTH = shake128 v_OUTPUT_LENGTH input out in
      out
  }

val shake256 (v_OUTPUT_LENGTH: usize) (input: t_Slice u8) (out: t_Array u8 v_OUTPUT_LENGTH)
    : Prims.Pure (t_Array u8 v_OUTPUT_LENGTH) Prims.l_True (fun _ -> Prims.l_True)

val shake256_absorb (st: t_Shake256Absorb) (input: t_Slice u8)
    : Prims.Pure t_Shake256Absorb Prims.l_True (fun _ -> Prims.l_True)

val shake256_absorb_final (st: t_Shake256Absorb) (input: t_Slice u8)
    : Prims.Pure t_Shake256Squeeze Prims.l_True (fun _ -> Prims.l_True)

val shake256_init: Prims.unit -> Prims.Pure t_Shake256Absorb Prims.l_True (fun _ -> Prims.l_True)

val shake256_squeeze (st: t_Shake256Squeeze) (out: t_Slice u8)
    : Prims.Pure (t_Shake256Squeeze & t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_first_block_shake256 (state: t_Shake256)
    : Prims.Pure (t_Shake256 & t_Array u8 (sz 136)) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_first_block_x4 (state: t_Shake256X4)
    : Prims.Pure
      (t_Shake256X4 &
        (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
      Prims.l_True
      (fun _ -> Prims.l_True)

val squeeze_first_five_blocks (state: t_Shake128X4) (out0 out1 out2 out3: t_Array u8 (sz 840))
    : Prims.Pure
      (t_Shake128X4 & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
        t_Array u8 (sz 840)) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_next_block (state: t_Shake128X4)
    : Prims.Pure
      (t_Shake128X4 &
        (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168)))
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 t_Shake128X4 =
  {
    f_init_absorb_pre
    =
    (fun (input0: t_Slice u8) (input1: t_Slice u8) (input2: t_Slice u8) (input3: t_Slice u8) -> true
    );
    f_init_absorb_post
    =
    (fun
        (input0: t_Slice u8)
        (input1: t_Slice u8)
        (input2: t_Slice u8)
        (input3: t_Slice u8)
        (out: t_Shake128X4)
        ->
        true);
    f_init_absorb
    =
    (fun (input0: t_Slice u8) (input1: t_Slice u8) (input2: t_Slice u8) (input3: t_Slice u8) ->
        init_absorb input0 input1 input2 input3);
    f_squeeze_first_five_blocks_pre
    =
    (fun
        (self: t_Shake128X4)
        (out0: t_Array u8 (sz 840))
        (out1: t_Array u8 (sz 840))
        (out2: t_Array u8 (sz 840))
        (out3: t_Array u8 (sz 840))
        ->
        true);
    f_squeeze_first_five_blocks_post
    =
    (fun
        (self: t_Shake128X4)
        (out0: t_Array u8 (sz 840))
        (out1: t_Array u8 (sz 840))
        (out2: t_Array u8 (sz 840))
        (out3: t_Array u8 (sz 840))
        (out4:
          (t_Shake128X4 & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
            t_Array u8 (sz 840)))
        ->
        true);
    f_squeeze_first_five_blocks
    =
    (fun
        (self: t_Shake128X4)
        (out0: t_Array u8 (sz 840))
        (out1: t_Array u8 (sz 840))
        (out2: t_Array u8 (sz 840))
        (out3: t_Array u8 (sz 840))
        ->
        let tmp0, tmp1, tmp2, tmp3, tmp4:(t_Shake128X4 & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
          t_Array u8 (sz 840) &
          t_Array u8 (sz 840)) =
          squeeze_first_five_blocks self out0 out1 out2 out3
        in
        let self:t_Shake128X4 = tmp0 in
        let out0:t_Array u8 (sz 840) = tmp1 in
        let out1:t_Array u8 (sz 840) = tmp2 in
        let out2:t_Array u8 (sz 840) = tmp3 in
        let out3:t_Array u8 (sz 840) = tmp4 in
        let _:Prims.unit = () in
        self, out0, out1, out2, out3
        <:
        (t_Shake128X4 & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
          t_Array u8 (sz 840)));
    f_squeeze_next_block_pre = (fun (self: t_Shake128X4) -> true);
    f_squeeze_next_block_post
    =
    (fun
        (self: t_Shake128X4)
        (out5:
          (t_Shake128X4 &
            (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168)))
        )
        ->
        true);
    f_squeeze_next_block
    =
    fun (self: t_Shake128X4) ->
      let tmp0, out4:(t_Shake128X4 &
        (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168))) =
        squeeze_next_block self
      in
      let self:t_Shake128X4 = tmp0 in
      let hax_temp_output:(t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) &
        t_Array u8 (sz 168)) =
        out4
      in
      self, hax_temp_output
      <:
      (t_Shake128X4 &
        (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168)))
  }

val squeeze_next_block_shake256 (state: t_Shake256)
    : Prims.Pure (t_Shake256 & t_Array u8 (sz 136)) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof t_Shake256 =
  {
    f_shake256_pre
    =
    (fun (v_OUTPUT_LENGTH: usize) (input: t_Slice u8) (out: t_Array u8 v_OUTPUT_LENGTH) -> true);
    f_shake256_post
    =
    (fun
        (v_OUTPUT_LENGTH: usize)
        (input: t_Slice u8)
        (out: t_Array u8 v_OUTPUT_LENGTH)
        (out1: t_Array u8 v_OUTPUT_LENGTH)
        ->
        true);
    f_shake256
    =
    (fun (v_OUTPUT_LENGTH: usize) (input: t_Slice u8) (out: t_Array u8 v_OUTPUT_LENGTH) ->
        let out:t_Array u8 v_OUTPUT_LENGTH = shake256 v_OUTPUT_LENGTH input out in
        out);
    f_init_absorb_pre = (fun (input: t_Slice u8) -> true);
    f_init_absorb_post = (fun (input: t_Slice u8) (out: t_Shake256) -> true);
    f_init_absorb = (fun (input: t_Slice u8) -> init_absorb_shake256 input);
    f_squeeze_first_block_pre = (fun (self: t_Shake256) -> true);
    f_squeeze_first_block_post
    =
    (fun (self: t_Shake256) (out2: (t_Shake256 & t_Array u8 (sz 136))) -> true);
    f_squeeze_first_block
    =
    (fun (self: t_Shake256) ->
        let tmp0, out1:(t_Shake256 & t_Array u8 (sz 136)) = squeeze_first_block_shake256 self in
        let self:t_Shake256 = tmp0 in
        let hax_temp_output:t_Array u8 (sz 136) = out1 in
        self, hax_temp_output <: (t_Shake256 & t_Array u8 (sz 136)));
    f_squeeze_next_block_pre = (fun (self: t_Shake256) -> true);
    f_squeeze_next_block_post
    =
    (fun (self: t_Shake256) (out2: (t_Shake256 & t_Array u8 (sz 136))) -> true);
    f_squeeze_next_block
    =
    fun (self: t_Shake256) ->
      let tmp0, out1:(t_Shake256 & t_Array u8 (sz 136)) = squeeze_next_block_shake256 self in
      let self:t_Shake256 = tmp0 in
      let hax_temp_output:t_Array u8 (sz 136) = out1 in
      self, hax_temp_output <: (t_Shake256 & t_Array u8 (sz 136))
  }

val squeeze_next_block_x4 (state: t_Shake256X4)
    : Prims.Pure
      (t_Shake256X4 &
        (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 t_Shake256X4 =
  {
    f_init_absorb_x4_pre
    =
    (fun (input0: t_Slice u8) (input1: t_Slice u8) (input2: t_Slice u8) (input3: t_Slice u8) -> true
    );
    f_init_absorb_x4_post
    =
    (fun
        (input0: t_Slice u8)
        (input1: t_Slice u8)
        (input2: t_Slice u8)
        (input3: t_Slice u8)
        (out: t_Shake256X4)
        ->
        true);
    f_init_absorb_x4
    =
    (fun (input0: t_Slice u8) (input1: t_Slice u8) (input2: t_Slice u8) (input3: t_Slice u8) ->
        init_absorb_x4 input0 input1 input2 input3);
    f_squeeze_first_block_x4_pre = (fun (self: t_Shake256X4) -> true);
    f_squeeze_first_block_x4_post
    =
    (fun
        (self: t_Shake256X4)
        (out5:
          (t_Shake256X4 &
            (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
        )
        ->
        true);
    f_squeeze_first_block_x4
    =
    (fun (self: t_Shake256X4) ->
        let tmp0, out4:(t_Shake256X4 &
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))) =
          squeeze_first_block_x4 self
        in
        let self:t_Shake256X4 = tmp0 in
        let hax_temp_output:(t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          out4
        in
        self, hax_temp_output
        <:
        (t_Shake256X4 &
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))));
    f_squeeze_next_block_x4_pre = (fun (self: t_Shake256X4) -> true);
    f_squeeze_next_block_x4_post
    =
    (fun
        (self: t_Shake256X4)
        (out5:
          (t_Shake256X4 &
            (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
        )
        ->
        true);
    f_squeeze_next_block_x4
    =
    (fun (self: t_Shake256X4) ->
        let tmp0, out4:(t_Shake256X4 &
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))) =
          squeeze_next_block_x4 self
        in
        let self:t_Shake256X4 = tmp0 in
        let hax_temp_output:(t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          out4
        in
        self, hax_temp_output
        <:
        (t_Shake256X4 &
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))));
    f_shake256_x4_pre
    =
    (fun
        (v_OUT_LEN: usize)
        (input0: t_Slice u8)
        (input1: t_Slice u8)
        (input2: t_Slice u8)
        (input3: t_Slice u8)
        (out0: t_Array u8 v_OUT_LEN)
        (out1: t_Array u8 v_OUT_LEN)
        (out2: t_Array u8 v_OUT_LEN)
        (out3: t_Array u8 v_OUT_LEN)
        ->
        true);
    f_shake256_x4_post
    =
    (fun
        (v_OUT_LEN: usize)
        (input0: t_Slice u8)
        (input1: t_Slice u8)
        (input2: t_Slice u8)
        (input3: t_Slice u8)
        (out0: t_Array u8 v_OUT_LEN)
        (out1: t_Array u8 v_OUT_LEN)
        (out2: t_Array u8 v_OUT_LEN)
        (out3: t_Array u8 v_OUT_LEN)
        (out4:
          (t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN
          ))
        ->
        true);
    f_shake256_x4
    =
    fun
      (v_OUT_LEN: usize)
      (input0: t_Slice u8)
      (input1: t_Slice u8)
      (input2: t_Slice u8)
      (input3: t_Slice u8)
      (out0: t_Array u8 v_OUT_LEN)
      (out1: t_Array u8 v_OUT_LEN)
      (out2: t_Array u8 v_OUT_LEN)
      (out3: t_Array u8 v_OUT_LEN)
      ->
      let out0:t_Array u8 v_OUT_LEN = shake256 v_OUT_LEN input0 out0 in
      let out1:t_Array u8 v_OUT_LEN = shake256 v_OUT_LEN input1 out1 in
      let out2:t_Array u8 v_OUT_LEN = shake256 v_OUT_LEN input2 out2 in
      let out3:t_Array u8 v_OUT_LEN = shake256 v_OUT_LEN input3 out3 in
      out0, out1, out2, out3
      <:
      (t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN)
  }
