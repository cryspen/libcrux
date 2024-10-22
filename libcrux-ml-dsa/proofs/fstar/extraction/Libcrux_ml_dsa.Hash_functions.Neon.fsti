module Libcrux_ml_dsa.Hash_functions.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

type t_Shake128x4 = { f_state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState (sz 2) }

/// Neon SHAKE 256 x4 state
type t_Shake256x4 = { f_state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState (sz 2) }

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
        let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState (sz 2) =
          let list =
            [Libcrux_sha3.Neon.X2.Incremental.init (); Libcrux_sha3.Neon.X2.Incremental.init ()]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list
        in
        let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState (sz 2) =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
            (sz 0)
            (Libcrux_sha3.Neon.X2.Incremental.shake128_absorb_final (state.[ sz 0 ]
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
                input0
                input1
              <:
              Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
        in
        let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState (sz 2) =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
            (sz 1)
            (Libcrux_sha3.Neon.X2.Incremental.shake128_absorb_final (state.[ sz 1 ]
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
                input2
                input3
              <:
              Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
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
        let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState & t_Array u8 (sz 840) &
          t_Array u8 (sz 840)) =
          Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_first_five_blocks (self.f_state.[ sz 0 ]
              <:
              Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
            out0
            out1
        in
        let self:t_Shake128x4 =
          {
            self with
            f_state
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_state (sz 0) tmp0
          }
          <:
          t_Shake128x4
        in
        let out0:t_Array u8 (sz 840) = tmp1 in
        let out1:t_Array u8 (sz 840) = tmp2 in
        let _:Prims.unit = () in
        let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState & t_Array u8 (sz 840) &
          t_Array u8 (sz 840)) =
          Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_first_five_blocks (self.f_state.[ sz 1 ]
              <:
              Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
            out2
            out3
        in
        let self:t_Shake128x4 =
          {
            self with
            f_state
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_state (sz 1) tmp0
          }
          <:
          t_Shake128x4
        in
        let out2:t_Array u8 (sz 840) = tmp1 in
        let out3:t_Array u8 (sz 840) = tmp2 in
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
      let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState & t_Array u8 (sz 168) &
        t_Array u8 (sz 168)) =
        Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_next_block (self.f_state.[ sz 0 ]
            <:
            Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
          out0
          out1
      in
      let self:t_Shake128x4 =
        {
          self with
          f_state
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_state (sz 0) tmp0
        }
        <:
        t_Shake128x4
      in
      let out0:t_Array u8 (sz 168) = tmp1 in
      let out1:t_Array u8 (sz 168) = tmp2 in
      let _:Prims.unit = () in
      let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState & t_Array u8 (sz 168) &
        t_Array u8 (sz 168)) =
        Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_next_block (self.f_state.[ sz 1 ]
            <:
            Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
          out2
          out3
      in
      let self:t_Shake128x4 =
        {
          self with
          f_state
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_state (sz 1) tmp0
        }
        <:
        t_Shake128x4
      in
      let out2:t_Array u8 (sz 168) = tmp1 in
      let out3:t_Array u8 (sz 168) = tmp2 in
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

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 t_Shake256x4 =
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
        (out: t_Shake256x4)
        ->
        true);
    f_init_absorb_x4
    =
    (fun (input0: t_Slice u8) (input1: t_Slice u8) (input2: t_Slice u8) (input3: t_Slice u8) ->
        let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState (sz 2) =
          let list =
            [Libcrux_sha3.Neon.X2.Incremental.init (); Libcrux_sha3.Neon.X2.Incremental.init ()]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list
        in
        let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState (sz 2) =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
            (sz 0)
            (Libcrux_sha3.Neon.X2.Incremental.shake256_absorb_final (state.[ sz 0 ]
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
                input0
                input1
              <:
              Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
        in
        let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState (sz 2) =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
            (sz 1)
            (Libcrux_sha3.Neon.X2.Incremental.shake256_absorb_final (state.[ sz 1 ]
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
                input2
                input3
              <:
              Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
        in
        { f_state = state } <: t_Shake256x4);
    f_squeeze_first_block_x4_pre = (fun (self: t_Shake256x4) -> true);
    f_squeeze_first_block_x4_post
    =
    (fun
        (self: t_Shake256x4)
        (out4:
          (t_Shake256x4 &
            (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
        )
        ->
        true);
    f_squeeze_first_block_x4
    =
    (fun (self: t_Shake256x4) ->
        let out0:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out1:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out2:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out3:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState & t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          Libcrux_sha3.Neon.X2.Incremental.shake256_squeeze_first_block (self.f_state.[ sz 0 ]
              <:
              Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
            out0
            out1
        in
        let self:t_Shake256x4 =
          {
            self with
            f_state
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_state (sz 0) tmp0
          }
          <:
          t_Shake256x4
        in
        let out0:t_Array u8 (sz 136) = tmp1 in
        let out1:t_Array u8 (sz 136) = tmp2 in
        let _:Prims.unit = () in
        let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState & t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          Libcrux_sha3.Neon.X2.Incremental.shake256_squeeze_first_block (self.f_state.[ sz 1 ]
              <:
              Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
            out2
            out3
        in
        let self:t_Shake256x4 =
          {
            self with
            f_state
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_state (sz 1) tmp0
          }
          <:
          t_Shake256x4
        in
        let out2:t_Array u8 (sz 136) = tmp1 in
        let out3:t_Array u8 (sz 136) = tmp2 in
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
    f_squeeze_next_block_x4_pre = (fun (self: t_Shake256x4) -> true);
    f_squeeze_next_block_x4_post
    =
    (fun
        (self: t_Shake256x4)
        (out4:
          (t_Shake256x4 &
            (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
        )
        ->
        true);
    f_squeeze_next_block_x4
    =
    (fun (self: t_Shake256x4) ->
        let out0:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out1:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out2:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let out3:t_Array u8 (sz 136) = Rust_primitives.Hax.repeat 0uy (sz 136) in
        let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState & t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          Libcrux_sha3.Neon.X2.Incremental.shake256_squeeze_next_block (self.f_state.[ sz 0 ]
              <:
              Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
            out0
            out1
        in
        let self:t_Shake256x4 =
          {
            self with
            f_state
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_state (sz 0) tmp0
          }
          <:
          t_Shake256x4
        in
        let out0:t_Array u8 (sz 136) = tmp1 in
        let out1:t_Array u8 (sz 136) = tmp2 in
        let _:Prims.unit = () in
        let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState & t_Array u8 (sz 136) &
          t_Array u8 (sz 136)) =
          Libcrux_sha3.Neon.X2.Incremental.shake256_squeeze_next_block (self.f_state.[ sz 1 ]
              <:
              Libcrux_sha3.Neon.X2.Incremental.t_KeccakState)
            out2
            out3
        in
        let self:t_Shake256x4 =
          {
            self with
            f_state
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_state (sz 1) tmp0
          }
          <:
          t_Shake256x4
        in
        let out2:t_Array u8 (sz 136) = tmp1 in
        let out3:t_Array u8 (sz 136) = tmp2 in
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
      let tmp0, tmp1:(t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN) =
        Libcrux_sha3.Neon.X2.shake256 input0 input1 out0 out1
      in
      let out0:t_Array u8 v_OUT_LEN = tmp0 in
      let out1:t_Array u8 v_OUT_LEN = tmp1 in
      let _:Prims.unit = () in
      let tmp0, tmp1:(t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN) =
        Libcrux_sha3.Neon.X2.shake256 input2 input3 out2 out3
      in
      let out2:t_Array u8 v_OUT_LEN = tmp0 in
      let out3:t_Array u8 v_OUT_LEN = tmp1 in
      let _:Prims.unit = () in
      out0, out1, out2, out3
      <:
      (t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN)
  }
