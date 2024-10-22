module Libcrux_ml_dsa.Hash_functions.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// Portable SHAKE 128 state
type t_Shake128 = | Shake128 : t_Shake128

/// Portable SHAKE 128 x4 state.
/// We're using a portable implementation so this is actually sequential.
type t_Shake128X4 = {
  f_state0:Libcrux_sha3.Portable.t_KeccakState;
  f_state1:Libcrux_sha3.Portable.t_KeccakState;
  f_state2:Libcrux_sha3.Portable.t_KeccakState;
  f_state3:Libcrux_sha3.Portable.t_KeccakState
}

/// Portable SHAKE 256 state
type t_Shake256 = { f_state:Libcrux_sha3.Portable.t_KeccakState }

/// Portable SHAKE 256 x4 state.
/// We're using a portable implementation so this is actually sequential.
type t_Shake256X4 = {
  f_state0:Libcrux_sha3.Portable.t_KeccakState;
  f_state1:Libcrux_sha3.Portable.t_KeccakState;
  f_state2:Libcrux_sha3.Portable.t_KeccakState;
  f_state3:Libcrux_sha3.Portable.t_KeccakState
}

val init_absorb__init_absorb (input: t_Slice u8)
    : Prims.Pure Libcrux_sha3.Portable.t_KeccakState Prims.l_True (fun _ -> Prims.l_True)

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
        let state0:Libcrux_sha3.Portable.t_KeccakState = init_absorb__init_absorb input0 in
        let state1:Libcrux_sha3.Portable.t_KeccakState = init_absorb__init_absorb input1 in
        let state2:Libcrux_sha3.Portable.t_KeccakState = init_absorb__init_absorb input2 in
        let state3:Libcrux_sha3.Portable.t_KeccakState = init_absorb__init_absorb input3 in
        { f_state0 = state0; f_state1 = state1; f_state2 = state2; f_state3 = state3 }
        <:
        t_Shake128X4);
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
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 840)) =
          Libcrux_sha3.Portable.Incremental.shake128_squeeze_first_five_blocks self.f_state0 out0
        in
        let self:t_Shake128X4 = { self with f_state0 = tmp0 } <: t_Shake128X4 in
        let out0:t_Array u8 (sz 840) = tmp1 in
        let _:Prims.unit = () in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 840)) =
          Libcrux_sha3.Portable.Incremental.shake128_squeeze_first_five_blocks self.f_state1 out1
        in
        let self:t_Shake128X4 = { self with f_state1 = tmp0 } <: t_Shake128X4 in
        let out1:t_Array u8 (sz 840) = tmp1 in
        let _:Prims.unit = () in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 840)) =
          Libcrux_sha3.Portable.Incremental.shake128_squeeze_first_five_blocks self.f_state2 out2
        in
        let self:t_Shake128X4 = { self with f_state2 = tmp0 } <: t_Shake128X4 in
        let out2:t_Array u8 (sz 840) = tmp1 in
        let _:Prims.unit = () in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 840)) =
          Libcrux_sha3.Portable.Incremental.shake128_squeeze_first_five_blocks self.f_state3 out3
        in
        let self:t_Shake128X4 = { self with f_state3 = tmp0 } <: t_Shake128X4 in
        let out3:t_Array u8 (sz 840) = tmp1 in
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
        (out4:
          (t_Shake128X4 &
            (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168)))
        )
        ->
        true);
    f_squeeze_next_block
    =
    fun (self: t_Shake128X4) ->
      let out0:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 168)) =
        Libcrux_sha3.Portable.Incremental.shake128_squeeze_next_block self.f_state0 out0
      in
      let self:t_Shake128X4 = { self with f_state0 = tmp0 } <: t_Shake128X4 in
      let out0:t_Array u8 (sz 168) = tmp1 in
      let _:Prims.unit = () in
      let out1:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 168)) =
        Libcrux_sha3.Portable.Incremental.shake128_squeeze_next_block self.f_state1 out1
      in
      let self:t_Shake128X4 = { self with f_state1 = tmp0 } <: t_Shake128X4 in
      let out1:t_Array u8 (sz 168) = tmp1 in
      let _:Prims.unit = () in
      let out2:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 168)) =
        Libcrux_sha3.Portable.Incremental.shake128_squeeze_next_block self.f_state2 out2
      in
      let self:t_Shake128X4 = { self with f_state2 = tmp0 } <: t_Shake128X4 in
      let out2:t_Array u8 (sz 168) = tmp1 in
      let _:Prims.unit = () in
      let out3:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 168)) =
        Libcrux_sha3.Portable.Incremental.shake128_squeeze_next_block self.f_state3 out3
      in
      let self:t_Shake128X4 = { self with f_state3 = tmp0 } <: t_Shake128X4 in
      let out3:t_Array u8 (sz 168) = tmp1 in
      let _:Prims.unit = () in
      let hax_temp_output:(t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) &
        t_Array u8 (sz 168)) =
        out0, out1, out2, out3
        <:
        (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168))
      in
      self, hax_temp_output
      <:
      (t_Shake128X4 &
        (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168)))
  }

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
      let out:t_Array u8 v_OUTPUT_LENGTH = Libcrux_sha3.Portable.shake128 out input in
      out
  }

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
        let out:t_Array u8 v_OUTPUT_LENGTH = Libcrux_sha3.Portable.shake256 out input in
        out);
    f_init_absorb_pre = (fun (input: t_Slice u8) -> true);
    f_init_absorb_post = (fun (input: t_Slice u8) (out: t_Shake256) -> true);
    f_init_absorb
    =
    (fun (input: t_Slice u8) ->
        let state:Libcrux_sha3.Portable.t_KeccakState =
          Libcrux_sha3.Portable.Incremental.shake256_init ()
        in
        let state:Libcrux_sha3.Portable.t_KeccakState =
          Libcrux_sha3.Portable.Incremental.shake256_absorb_final state input
        in
        { f_state = state } <: t_Shake256);
    f_squeeze_first_block_pre = (fun (self: t_Shake256) -> true);
    f_squeeze_first_block_post
    =
    (fun (self: t_Shake256) (out1: (t_Shake256 & t_Array u8 (sz 136))) -> true);
    f_squeeze_first_block
    =
    (fun (self: t_Shake256) ->
        let out:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 136)) =
          Libcrux_sha3.Portable.Incremental.shake256_squeeze_first_block self.f_state out
        in
        let self:t_Shake256 = { self with f_state = tmp0 } <: t_Shake256 in
        let out:t_Array u8 (sz 136) = tmp1 in
        let _:Prims.unit = () in
        let hax_temp_output:t_Array u8 (sz 136) = out in
        self, hax_temp_output <: (t_Shake256 & t_Array u8 (sz 136)));
    f_squeeze_next_block_pre = (fun (self: t_Shake256) -> true);
    f_squeeze_next_block_post
    =
    (fun (self: t_Shake256) (out1: (t_Shake256 & t_Array u8 (sz 136))) -> true);
    f_squeeze_next_block
    =
    fun (self: t_Shake256) ->
      let out:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
      let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 136)) =
        Libcrux_sha3.Portable.Incremental.shake256_squeeze_next_block self.f_state out
      in
      let self:t_Shake256 = { self with f_state = tmp0 } <: t_Shake256 in
      let out:t_Array u8 (sz 136) = tmp1 in
      let _:Prims.unit = () in
      let hax_temp_output:t_Array u8 (sz 136) = out in
      self, hax_temp_output <: (t_Shake256 & t_Array u8 (sz 136))
  }

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
        let state0:Libcrux_sha3.Portable.t_KeccakState =
          Libcrux_sha3.Portable.Incremental.shake256_init ()
        in
        let state0:Libcrux_sha3.Portable.t_KeccakState =
          Libcrux_sha3.Portable.Incremental.shake256_absorb_final state0 input0
        in
        let state1:Libcrux_sha3.Portable.t_KeccakState =
          Libcrux_sha3.Portable.Incremental.shake256_init ()
        in
        let state1:Libcrux_sha3.Portable.t_KeccakState =
          Libcrux_sha3.Portable.Incremental.shake256_absorb_final state1 input1
        in
        let state2:Libcrux_sha3.Portable.t_KeccakState =
          Libcrux_sha3.Portable.Incremental.shake256_init ()
        in
        let state2:Libcrux_sha3.Portable.t_KeccakState =
          Libcrux_sha3.Portable.Incremental.shake256_absorb_final state2 input2
        in
        let state3:Libcrux_sha3.Portable.t_KeccakState =
          Libcrux_sha3.Portable.Incremental.shake256_init ()
        in
        let state3:Libcrux_sha3.Portable.t_KeccakState =
          Libcrux_sha3.Portable.Incremental.shake256_absorb_final state3 input3
        in
        { f_state0 = state0; f_state1 = state1; f_state2 = state2; f_state3 = state3 }
        <:
        t_Shake256X4);
    f_squeeze_first_block_x4_pre = (fun (self: t_Shake256X4) -> true);
    f_squeeze_first_block_x4_post
    =
    (fun
        (self: t_Shake256X4)
        (out4:
          (t_Shake256X4 &
            (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
        )
        ->
        true);
    f_squeeze_first_block_x4
    =
    (fun (self: t_Shake256X4) ->
        let out0:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 136)) =
          Libcrux_sha3.Portable.Incremental.shake256_squeeze_first_block self.f_state0 out0
        in
        let self:t_Shake256X4 = { self with f_state0 = tmp0 } <: t_Shake256X4 in
        let out0:t_Array u8 (sz 136) = tmp1 in
        let _:Prims.unit = () in
        let out1:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 136)) =
          Libcrux_sha3.Portable.Incremental.shake256_squeeze_first_block self.f_state1 out1
        in
        let self:t_Shake256X4 = { self with f_state1 = tmp0 } <: t_Shake256X4 in
        let out1:t_Array u8 (sz 136) = tmp1 in
        let _:Prims.unit = () in
        let out2:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 136)) =
          Libcrux_sha3.Portable.Incremental.shake256_squeeze_first_block self.f_state2 out2
        in
        let self:t_Shake256X4 = { self with f_state2 = tmp0 } <: t_Shake256X4 in
        let out2:t_Array u8 (sz 136) = tmp1 in
        let _:Prims.unit = () in
        let out3:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 136)) =
          Libcrux_sha3.Portable.Incremental.shake256_squeeze_first_block self.f_state3 out3
        in
        let self:t_Shake256X4 = { self with f_state3 = tmp0 } <: t_Shake256X4 in
        let out3:t_Array u8 (sz 136) = tmp1 in
        let _:Prims.unit = () in
        let hax_temp_output:(t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          out0, out1, out2, out3
          <:
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))
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
        (out4:
          (t_Shake256X4 &
            (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
        )
        ->
        true);
    f_squeeze_next_block_x4
    =
    (fun (self: t_Shake256X4) ->
        let out0:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 136)) =
          Libcrux_sha3.Portable.Incremental.shake256_squeeze_next_block self.f_state0 out0
        in
        let self:t_Shake256X4 = { self with f_state0 = tmp0 } <: t_Shake256X4 in
        let out0:t_Array u8 (sz 136) = tmp1 in
        let _:Prims.unit = () in
        let out1:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 136)) =
          Libcrux_sha3.Portable.Incremental.shake256_squeeze_next_block self.f_state1 out1
        in
        let self:t_Shake256X4 = { self with f_state1 = tmp0 } <: t_Shake256X4 in
        let out1:t_Array u8 (sz 136) = tmp1 in
        let _:Prims.unit = () in
        let out2:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 136)) =
          Libcrux_sha3.Portable.Incremental.shake256_squeeze_next_block self.f_state2 out2
        in
        let self:t_Shake256X4 = { self with f_state2 = tmp0 } <: t_Shake256X4 in
        let out2:t_Array u8 (sz 136) = tmp1 in
        let _:Prims.unit = () in
        let out3:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 136)) =
          Libcrux_sha3.Portable.Incremental.shake256_squeeze_next_block self.f_state3 out3
        in
        let self:t_Shake256X4 = { self with f_state3 = tmp0 } <: t_Shake256X4 in
        let out3:t_Array u8 (sz 136) = tmp1 in
        let _:Prims.unit = () in
        let hax_temp_output:(t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          out0, out1, out2, out3
          <:
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))
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
      let out0:t_Array u8 v_OUT_LEN = Libcrux_sha3.Portable.shake256 out0 input0 in
      let out1:t_Array u8 v_OUT_LEN = Libcrux_sha3.Portable.shake256 out1 input1 in
      let out2:t_Array u8 v_OUT_LEN = Libcrux_sha3.Portable.shake256 out2 input2 in
      let out3:t_Array u8 v_OUT_LEN = Libcrux_sha3.Portable.shake256 out3 input3 in
      out0, out1, out2, out3
      <:
      (t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN)
  }
