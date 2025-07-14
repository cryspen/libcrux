module Libcrux_sha3.Simd.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Traits in
  ()

let rotate_left (v_LEFT v_RIGHT: i32) (x: u64) =
  let _:Prims.unit =
    if false
    then
      let _:Prims.unit = Hax_lib.v_assert ((v_LEFT +! v_RIGHT <: i32) =. mk_i32 64 <: bool) in
      ()
  in
  Core.Num.impl_u64__rotate_left x (cast (v_LEFT <: i32) <: u32)

let e_veor5q_u64 (a b c d e: u64) = (((a ^. b <: u64) ^. c <: u64) ^. d <: u64) ^. e

let e_vrax1q_u64 (a b: u64) = a ^. (rotate_left (mk_i32 1) (mk_i32 63) b <: u64)

let e_vxarq_u64 (v_LEFT v_RIGHT: i32) (a b: u64) = rotate_left v_LEFT v_RIGHT (a ^. b <: u64)

let e_vbcaxq_u64 (a b c: u64) = a ^. (b &. (~.c <: u64) <: u64)

let e_veorq_n_u64 (a c: u64) = a ^. c

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_sha3.Traits.t_KeccakItem u64 (mk_usize 1) =
  {
    _super_15837849249852401974 = FStar.Tactics.Typeclasses.solve;
    _super_14902616874729899161 = FStar.Tactics.Typeclasses.solve;
    f_zero_pre = (fun (_: Prims.unit) -> true);
    f_zero_post = (fun (_: Prims.unit) (out: u64) -> true);
    f_zero = (fun (_: Prims.unit) -> mk_u64 0);
    f_xor5_pre = (fun (a: u64) (b: u64) (c: u64) (d: u64) (e: u64) -> true);
    f_xor5_post = (fun (a: u64) (b: u64) (c: u64) (d: u64) (e: u64) (out: u64) -> true);
    f_xor5 = (fun (a: u64) (b: u64) (c: u64) (d: u64) (e: u64) -> e_veor5q_u64 a b c d e);
    f_rotate_left1_and_xor_pre = (fun (a: u64) (b: u64) -> true);
    f_rotate_left1_and_xor_post = (fun (a: u64) (b: u64) (out: u64) -> true);
    f_rotate_left1_and_xor = (fun (a: u64) (b: u64) -> e_vrax1q_u64 a b);
    f_xor_and_rotate_pre = (fun (v_LEFT: i32) (v_RIGHT: i32) (a: u64) (b: u64) -> true);
    f_xor_and_rotate_post = (fun (v_LEFT: i32) (v_RIGHT: i32) (a: u64) (b: u64) (out: u64) -> true);
    f_xor_and_rotate
    =
    (fun (v_LEFT: i32) (v_RIGHT: i32) (a: u64) (b: u64) -> e_vxarq_u64 v_LEFT v_RIGHT a b);
    f_and_not_xor_pre = (fun (a: u64) (b: u64) (c: u64) -> true);
    f_and_not_xor_post = (fun (a: u64) (b: u64) (c: u64) (out: u64) -> true);
    f_and_not_xor = (fun (a: u64) (b: u64) (c: u64) -> e_vbcaxq_u64 a b c);
    f_xor_constant_pre = (fun (a: u64) (c: u64) -> true);
    f_xor_constant_post = (fun (a: u64) (c: u64) (out: u64) -> true);
    f_xor_constant = (fun (a: u64) (c: u64) -> e_veorq_n_u64 a c);
    f_xor_pre = (fun (a: u64) (b: u64) -> true);
    f_xor_post = (fun (a: u64) (b: u64) (out: u64) -> true);
    f_xor = fun (a: u64) (b: u64) -> a ^. b
  }

let load_block
      (v_RATE: usize)
      (state: t_Array u64 (mk_usize 25))
      (blocks: t_Slice u8)
      (start: usize)
     =
  let _:Prims.unit =
    if false
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((start <=. ((Core.Slice.impl__len #u8 blocks <: usize) -! v_RATE <: usize)
              <:
              bool) &&
            ((v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 <: bool))
      in
      ()
  in
  let state_flat:t_Array u64 (mk_usize 25) = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
  let state_flat:t_Array u64 (mk_usize 25) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (v_RATE /! mk_usize 8 <: usize)
      (fun state_flat temp_1_ ->
          let state_flat:t_Array u64 (mk_usize 25) = state_flat in
          let _:usize = temp_1_ in
          true)
      state_flat
      (fun state_flat i ->
          let state_flat:t_Array u64 (mk_usize 25) = state_flat in
          let i:usize = i in
          let offset:usize = start +! (mk_usize 8 *! i <: usize) in
          let state_flat:t_Array u64 (mk_usize 25) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state_flat
              i
              (Core.Num.impl_u64__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (mk_usize 8))
                      #Core.Array.t_TryFromSliceError
                      (Core.Convert.f_try_into #(t_Slice u8)
                          #(t_Array u8 (mk_usize 8))
                          #FStar.Tactics.Typeclasses.solve
                          (blocks.[ {
                                Core.Ops.Range.f_start = offset;
                                Core.Ops.Range.f_end = offset +! mk_usize 8 <: usize
                              }
                              <:
                              Core.Ops.Range.t_Range usize ]
                            <:
                            t_Slice u8)
                        <:
                        Core.Result.t_Result (t_Array u8 (mk_usize 8))
                          Core.Array.t_TryFromSliceError)
                    <:
                    t_Array u8 (mk_usize 8))
                <:
                u64)
          in
          state_flat)
  in
  let state:t_Array u64 (mk_usize 25) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (v_RATE /! mk_usize 8 <: usize)
      (fun state temp_1_ ->
          let state:t_Array u64 (mk_usize 25) = state in
          let _:usize = temp_1_ in
          true)
      state
      (fun state i ->
          let state:t_Array u64 (mk_usize 25) = state in
          let i:usize = i in
          Libcrux_sha3.Traits.set_ij (mk_usize 1)
            #u64
            state
            (i /! mk_usize 5 <: usize)
            (i %! mk_usize 5 <: usize)
            ((Libcrux_sha3.Traits.get_ij (mk_usize 1)
                  #u64
                  state
                  (i /! mk_usize 5 <: usize)
                  (i %! mk_usize 5 <: usize)
                <:
                u64) ^.
              (state_flat.[ i ] <: u64)
              <:
              u64)
          <:
          t_Array u64 (mk_usize 25))
  in
  state

let load_last
      (v_RATE: usize)
      (v_DELIMITER: u8)
      (state: t_Array u64 (mk_usize 25))
      (blocks: t_Slice u8)
      (start len: usize)
     =
  let _:Prims.unit =
    if false
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((start +! len <: usize) <=. (Core.Slice.impl__len #u8 blocks <: usize)
            <:
            bool)
      in
      ()
  in
  let buffer:t_Array u8 v_RATE = Rust_primitives.Hax.repeat (mk_u8 0) v_RATE in
  let buffer:t_Array u8 v_RATE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range buffer
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = len }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (buffer.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = len }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (blocks.[ { Core.Ops.Range.f_start = start; Core.Ops.Range.f_end = start +! len <: usize }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let buffer:t_Array u8 v_RATE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize buffer len v_DELIMITER
  in
  let buffer:t_Array u8 v_RATE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize buffer
      (v_RATE -! mk_usize 1 <: usize)
      ((buffer.[ v_RATE -! mk_usize 1 <: usize ] <: u8) |. mk_u8 128 <: u8)
  in
  let state:t_Array u64 (mk_usize 25) =
    load_block v_RATE state (buffer <: t_Slice u8) (mk_usize 0)
  in
  state

#push-options "--fuel 20 --ifuel 20 --z3rlimit 6000"

let store_block (v_RATE: usize) (s: t_Array u64 (mk_usize 25)) (out: t_Slice u8) (start len: usize) =
  let out_len = (Core.Slice.impl__len #u8 out) in 
  assume (start <. out_len);
  assume (len <. out_len);
  assume (start +. len <=. out_len);
  let octets:usize = len /! mk_usize 8 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      octets
      (fun out temp_1_ ->
          let out:t_Slice u8 = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          assume (i /! mk_usize 5 <. mk_usize 5);
          assume (start <. Core.Num.impl_usize__MAX -! (mk_usize 8 *! i));
          assume (start +! (mk_usize 8 *! i) <. Core.Num.impl_usize__MAX);
          let out:t_Slice u8 = out in
          let i:usize = i in
          let value:u64 =
            Libcrux_sha3.Traits.get_ij (mk_usize 1)
              #u64
              s
              (i /! mk_usize 5 <: usize)
              (i %! mk_usize 5 <: usize)
          in
          let bytes:t_Array u8 (mk_usize 8) = Core.Num.impl_u64__to_le_bytes value in
          let out_pos:usize = start +! (mk_usize 8 *! i <: usize) in
          assume (out_pos <. out_len);
          assume (out_pos <=. out_len -! (mk_usize 8));
          assume (out_pos +! mk_usize 8 <=. out_len);
          assume (out_pos >=. mk_usize 0);
          let range: Core.Ops.Range.t_Range usize = { 
            Core.Ops.Range.f_start = out_pos; 
            Core.Ops.Range.f_end = out_pos +! mk_usize 8 
          } in
          assume (Core.Ops.Index.f_index_pre out range);
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range 
              out
              range 
              (Core.Slice.impl__copy_from_slice #u8
                  (out.[range])
                  bytes
              )
          in
          out)
  in
  let remaining:usize = len %! mk_usize 8 in
  let out:t_Slice u8 =
    if remaining >. mk_usize 0
    then
      let value:u64 =
        Libcrux_sha3.Traits.get_ij (mk_usize 1)
          #u64
          s
          (octets /! mk_usize 5 <: usize)
          (octets %! mk_usize 5 <: usize)
      in
      let bytes:t_Array u8 (mk_usize 8) = Core.Num.impl_u64__to_le_bytes value in
      let out_pos:usize = (start +! len <: usize) -! remaining in
      let out:t_Slice u8 =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
          ({
              Core.Ops.Range.f_start = out_pos;
              Core.Ops.Range.f_end = out_pos +! remaining <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
          (Core.Slice.impl__copy_from_slice #u8
              (out.[ {
                    Core.Ops.Range.f_start = out_pos;
                    Core.Ops.Range.f_end = out_pos +! remaining <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (bytes.[ { Core.Ops.Range.f_end = remaining } <: Core.Ops.Range.t_RangeTo usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      out
    else out
  in
  out

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Libcrux_sha3.Traits.t_Absorb
  (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64) (mk_usize 1) =
  {
    f_load_block_pre
    =
    (fun
        (v_RATE: usize)
        (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        (input: t_Array (t_Slice u8) (mk_usize 1))
        (start: usize)
        ->
        true);
    f_load_block_post
    =
    (fun
        (v_RATE: usize)
        (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        (input: t_Array (t_Slice u8) (mk_usize 1))
        (start: usize)
        (out: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        ->
        true);
    f_load_block
    =
    (fun
        (v_RATE: usize)
        (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        (input: t_Array (t_Slice u8) (mk_usize 1))
        (start: usize)
        ->
        let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
          {
            self with
            Libcrux_sha3.Generic_keccak.f_st
            =
            load_block v_RATE
              self.Libcrux_sha3.Generic_keccak.f_st
              (input.[ mk_usize 0 ] <: t_Slice u8)
              start
          }
          <:
          Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64
        in
        self);
    f_load_last_pre
    =
    (fun
        (v_RATE: usize)
        (v_DELIMITER: u8)
        (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        (input: t_Array (t_Slice u8) (mk_usize 1))
        (start: usize)
        (len: usize)
        ->
        true);
    f_load_last_post
    =
    (fun
        (v_RATE: usize)
        (v_DELIMITER: u8)
        (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        (input: t_Array (t_Slice u8) (mk_usize 1))
        (start: usize)
        (len: usize)
        (out: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        ->
        true);
    f_load_last
    =
    fun
      (v_RATE: usize)
      (v_DELIMITER: u8)
      (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (input: t_Array (t_Slice u8) (mk_usize 1))
      (start: usize)
      (len: usize)
      ->
      let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
        {
          self with
          Libcrux_sha3.Generic_keccak.f_st
          =
          load_last v_RATE
            v_DELIMITER
            self.Libcrux_sha3.Generic_keccak.f_st
            (input.[ mk_usize 0 ] <: t_Slice u8)
            start
            len
        }
        <:
        Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64
      in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Libcrux_sha3.Traits.t_Squeeze
  (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64) u64 =
  {
    f_squeeze_pre
    =
    (fun
        (v_RATE: usize)
        (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        (out: t_Slice u8)
        (start: usize)
        (len: usize)
        ->
        true);
    f_squeeze_post
    =
    (fun
        (v_RATE: usize)
        (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        (out: t_Slice u8)
        (start: usize)
        (len: usize)
        (out1: t_Slice u8)
        ->
        true);
    f_squeeze
    =
    fun
      (v_RATE: usize)
      (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (out: t_Slice u8)
      (start: usize)
      (len: usize)
      ->
      let out:t_Slice u8 = store_block v_RATE self.Libcrux_sha3.Generic_keccak.f_st out start len in
      out
  }
