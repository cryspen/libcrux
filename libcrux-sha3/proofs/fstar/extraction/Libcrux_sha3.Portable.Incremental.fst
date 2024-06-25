module Libcrux_sha3.Portable.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Portable_keccak in
  let open Libcrux_sha3.Traits in
  ()

let shake128_absorb_final (s: Libcrux_sha3.Portable.t_KeccakState1) (data0: t_Slice u8) =
  let s:Libcrux_sha3.Portable.t_KeccakState1 =
    {
      s with
      Libcrux_sha3.Portable.f_state
      =
      Libcrux_sha3.Generic_keccak.absorb_final (sz 1)
        #u64
        (sz 168)
        31uy
        s.Libcrux_sha3.Portable.f_state
        (let list = [data0] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
    }
    <:
    Libcrux_sha3.Portable.t_KeccakState1
  in
  s

let shake128_init (_: Prims.unit) =
  { Libcrux_sha3.Portable.f_state = Libcrux_sha3.Generic_keccak.impl_1__new (sz 1) #u64 () }
  <:
  Libcrux_sha3.Portable.t_KeccakState1

let shake128_squeeze_first_five_blocks
      (s: Libcrux_sha3.Portable.t_KeccakState1)
      (out0: t_Array u8 (sz 840))
     =
  let out1:t_Array (t_Array u8 (sz 840)) (sz 1) =
    let list = [Rust_primitives.Hax.repeat 0uy (sz 840)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list
  in
  let tmp0, tmp1:(Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64 &
    t_Array (t_Array u8 (sz 840)) (sz 1)) =
    Libcrux_sha3.Generic_keccak.squeeze_first_five_blocks (sz 1)
      #u64
      (sz 168)
      (sz 840)
      s.Libcrux_sha3.Portable.f_state
      out1
  in
  let s:Libcrux_sha3.Portable.t_KeccakState1 =
    { s with Libcrux_sha3.Portable.f_state = tmp0 } <: Libcrux_sha3.Portable.t_KeccakState1
  in
  let out1:t_Array (t_Array u8 (sz 840)) (sz 1) = tmp1 in
  let _:Prims.unit = () in
  let out0:t_Array u8 (sz 840) =
    Core.Slice.impl__copy_from_slice #u8
      out0
      ((out1.[ sz 0 ] <: t_Array u8 (sz 840)).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 840
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  s, out0 <: (Libcrux_sha3.Portable.t_KeccakState1 & t_Array u8 (sz 840))

let shake128_squeeze_first_three_blocks
      (s: Libcrux_sha3.Portable.t_KeccakState1)
      (out0: t_Array u8 (sz 504))
     =
  let out1:t_Array (t_Array u8 (sz 504)) (sz 1) =
    let list = [Rust_primitives.Hax.repeat 0uy (sz 504)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list
  in
  let tmp0, tmp1:(Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64 &
    t_Array (t_Array u8 (sz 504)) (sz 1)) =
    Libcrux_sha3.Generic_keccak.squeeze_first_three_blocks (sz 1)
      #u64
      (sz 168)
      (sz 504)
      s.Libcrux_sha3.Portable.f_state
      out1
  in
  let s:Libcrux_sha3.Portable.t_KeccakState1 =
    { s with Libcrux_sha3.Portable.f_state = tmp0 } <: Libcrux_sha3.Portable.t_KeccakState1
  in
  let out1:t_Array (t_Array u8 (sz 504)) (sz 1) = tmp1 in
  let _:Prims.unit = () in
  let out0:t_Array u8 (sz 504) =
    Core.Slice.impl__copy_from_slice #u8
      out0
      ((out1.[ sz 0 ] <: t_Array u8 (sz 504)).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 504
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  s, out0 <: (Libcrux_sha3.Portable.t_KeccakState1 & t_Array u8 (sz 504))

let shake128_squeeze_next_block
      (s: Libcrux_sha3.Portable.t_KeccakState1)
      (out0: t_Array u8 (sz 168))
     =
  let out1:t_Array (t_Array u8 (sz 168)) (sz 1) =
    let list = [Rust_primitives.Hax.repeat 0uy (sz 168)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list
  in
  let tmp0, tmp1:(Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64 &
    t_Array (t_Array u8 (sz 168)) (sz 1)) =
    Libcrux_sha3.Generic_keccak.squeeze_next_block (sz 1)
      #u64
      (sz 168)
      (sz 168)
      s.Libcrux_sha3.Portable.f_state
      out1
      (sz 0)
  in
  let s:Libcrux_sha3.Portable.t_KeccakState1 =
    { s with Libcrux_sha3.Portable.f_state = tmp0 } <: Libcrux_sha3.Portable.t_KeccakState1
  in
  let out1:t_Array (t_Array u8 (sz 168)) (sz 1) = tmp1 in
  let _:Prims.unit = () in
  let out0:t_Array u8 (sz 168) =
    Core.Slice.impl__copy_from_slice #u8
      out0
      ((out1.[ sz 0 ] <: t_Array u8 (sz 168)).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 168
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  s, out0 <: (Libcrux_sha3.Portable.t_KeccakState1 & t_Array u8 (sz 168))
