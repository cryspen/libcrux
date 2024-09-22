module Libcrux_ml_dsa.Hash_functions.Simd256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// AVX2 SHAKE 128 state
/// This only implements the XofX4 API. For the single Xof, the portable
/// version is used.
type t_Shake128x4 = { f_state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 t_Shake128x4 =
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
        (out: t_Shake128x4)
        ->
        true);
    f_init_absorb
    =
    (fun (input0: t_Slice u8) (input1: t_Slice u8) (input2: t_Slice u8) (input3: t_Slice u8) ->
        let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState =
          Libcrux_sha3.Avx2.X4.Incremental.init ()
        in
        let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState =
          Libcrux_sha3.Avx2.X4.Incremental.shake128_absorb_final state input0 input1 input2 input3
        in
        { f_state = state } <: t_Shake128x4);
    f_squeeze_first_five_blocks_pre
    =
    (fun
        (self: t_Shake128x4)
        (out0: t_Array u8 (sz 840))
        (out1: t_Array u8 (sz 840))
        (out2: t_Array u8 (sz 840))
        (out3: t_Array u8 (sz 840))
        ->
        true);
    f_squeeze_first_five_blocks_post
    =
    (fun
        (self: t_Shake128x4)
        (out0: t_Array u8 (sz 840))
        (out1: t_Array u8 (sz 840))
        (out2: t_Array u8 (sz 840))
        (out3: t_Array u8 (sz 840))
        (out4:
          (t_Shake128x4 & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
            t_Array u8 (sz 840)))
        ->
        true);
    f_squeeze_first_five_blocks
    =
    (fun
        (self: t_Shake128x4)
        (out0: t_Array u8 (sz 840))
        (out1: t_Array u8 (sz 840))
        (out2: t_Array u8 (sz 840))
        (out3: t_Array u8 (sz 840))
        ->
        let tmp0, tmp1, tmp2, tmp3, tmp4:(Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState &
          t_Array u8 (sz 840) &
          t_Array u8 (sz 840) &
          t_Array u8 (sz 840) &
          t_Array u8 (sz 840)) =
          Libcrux_sha3.Avx2.X4.Incremental.shake128_squeeze_first_five_blocks self.f_state
            out0
            out1
            out2
            out3
        in
        let self:t_Shake128x4 = { self with f_state = tmp0 } <: t_Shake128x4 in
        let out0:t_Array u8 (sz 840) = tmp1 in
        let out1:t_Array u8 (sz 840) = tmp2 in
        let out2:t_Array u8 (sz 840) = tmp3 in
        let out3:t_Array u8 (sz 840) = tmp4 in
        let _:Prims.unit = () in
        self, out0, out1, out2, out3
        <:
        (t_Shake128x4 & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
          t_Array u8 (sz 840)));
    f_squeeze_next_block_pre = (fun (self: t_Shake128x4) -> true);
    f_squeeze_next_block_post
    =
    (fun
        (self: t_Shake128x4)
        (out4:
          (t_Shake128x4 &
            (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168)))
        )
        ->
        true);
    f_squeeze_next_block
    =
    fun (self: t_Shake128x4) ->
      let out0:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let out1:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let out2:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let out3:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let tmp0, tmp1, tmp2, tmp3, tmp4:(Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState &
        t_Array u8 (sz 168) &
        t_Array u8 (sz 168) &
        t_Array u8 (sz 168) &
        t_Array u8 (sz 168)) =
        Libcrux_sha3.Avx2.X4.Incremental.shake128_squeeze_next_block self.f_state
          out0
          out1
          out2
          out3
      in
      let self:t_Shake128x4 = { self with f_state = tmp0 } <: t_Shake128x4 in
      let out0:t_Array u8 (sz 168) = tmp1 in
      let out1:t_Array u8 (sz 168) = tmp2 in
      let out2:t_Array u8 (sz 168) = tmp3 in
      let out3:t_Array u8 (sz 168) = tmp4 in
      let _:Prims.unit = () in
      let hax_temp_output:(t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) &
        t_Array u8 (sz 168)) =
        out0, out1, out2, out3
        <:
        (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168))
      in
      self, hax_temp_output
      <:
      (t_Shake128x4 &
        (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168)))
  }

/// AVX2 SHAKE 256 state
type t_Shake256 = { f_state:Libcrux_sha3.Portable.t_KeccakState }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof t_Shake256 =
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

/// AVX2 SHAKE 256 x4 state.
type t_Shake256x4 = { f_state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 t_Shake256x4 =
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
        (out: t_Shake256x4)
        ->
        true);
    f_init_absorb
    =
    (fun (input0: t_Slice u8) (input1: t_Slice u8) (input2: t_Slice u8) (input3: t_Slice u8) ->
        let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState =
          Libcrux_sha3.Avx2.X4.Incremental.init ()
        in
        let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState =
          Libcrux_sha3.Avx2.X4.Incremental.shake256_absorb_final state input0 input1 input2 input3
        in
        { f_state = state } <: t_Shake256x4);
    f_squeeze_first_block_pre = (fun (self: t_Shake256x4) -> true);
    f_squeeze_first_block_post
    =
    (fun
        (self: t_Shake256x4)
        (out4:
          (t_Shake256x4 &
            (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
        )
        ->
        true);
    f_squeeze_first_block
    =
    (fun (self: t_Shake256x4) ->
        let out0:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out1:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out2:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out3:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1, tmp2, tmp3, tmp4:(Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState &
          t_Array u8 (sz 136) &
          t_Array u8 (sz 136) &
          t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          Libcrux_sha3.Avx2.X4.Incremental.shake256_squeeze_first_block self.f_state
            out0
            out1
            out2
            out3
        in
        let self:t_Shake256x4 = { self with f_state = tmp0 } <: t_Shake256x4 in
        let out0:t_Array u8 (sz 136) = tmp1 in
        let out1:t_Array u8 (sz 136) = tmp2 in
        let out2:t_Array u8 (sz 136) = tmp3 in
        let out3:t_Array u8 (sz 136) = tmp4 in
        let _:Prims.unit = () in
        let hax_temp_output:(t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          out0, out1, out2, out3
          <:
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))
        in
        self, hax_temp_output
        <:
        (t_Shake256x4 &
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))));
    f_squeeze_next_block_pre = (fun (self: t_Shake256x4) -> true);
    f_squeeze_next_block_post
    =
    (fun
        (self: t_Shake256x4)
        (out4:
          (t_Shake256x4 &
            (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
        )
        ->
        true);
    f_squeeze_next_block
    =
    (fun (self: t_Shake256x4) ->
        let out0:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out1:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out2:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out3:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1, tmp2, tmp3, tmp4:(Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState &
          t_Array u8 (sz 136) &
          t_Array u8 (sz 136) &
          t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          Libcrux_sha3.Avx2.X4.Incremental.shake256_squeeze_next_block self.f_state
            out0
            out1
            out2
            out3
        in
        let self:t_Shake256x4 = { self with f_state = tmp0 } <: t_Shake256x4 in
        let out0:t_Array u8 (sz 136) = tmp1 in
        let out1:t_Array u8 (sz 136) = tmp2 in
        let out2:t_Array u8 (sz 136) = tmp3 in
        let out3:t_Array u8 (sz 136) = tmp4 in
        let _:Prims.unit = () in
        let hax_temp_output:(t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          out0, out1, out2, out3
          <:
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))
        in
        self, hax_temp_output
        <:
        (t_Shake256x4 &
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))));
    f_shake256_pre
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
    f_shake256_post
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
    f_shake256
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
      let tmp0, tmp1, tmp2, tmp3:(t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN &
        t_Array u8 v_OUT_LEN) =
        Libcrux_sha3.Avx2.X4.shake256 input0 input1 input2 input3 out0 out1 out2 out3
      in
      let out0:t_Array u8 v_OUT_LEN = tmp0 in
      let out1:t_Array u8 v_OUT_LEN = tmp1 in
      let out2:t_Array u8 v_OUT_LEN = tmp2 in
      let out3:t_Array u8 v_OUT_LEN = tmp3 in
      let _:Prims.unit = () in
      out0, out1, out2, out3
      <:
      (t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN)
  }
