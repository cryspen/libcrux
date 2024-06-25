module Libcrux_sha3.Neon.X2.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Simd.Arm64 in
  let open Libcrux_sha3.Traits in
  ()

let shake128_absorb_final (s: t_KeccakState2) (data0 data1: t_Slice u8) =
  let s:t_KeccakState2 =
    {
      s with
      f_state
      =
      Libcrux_sha3.Generic_keccak.absorb_final (sz 2)
        #Core.Core_arch.Arm_shared.Neon.t_uint64x2_t
        (sz 168)
        31uy
        s.f_state
        (let list = [data0; data1] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
    }
    <:
    t_KeccakState2
  in
  s

let shake128_init (_: Prims.unit) =
  {
    f_state
    =
    Libcrux_sha3.Generic_keccak.impl_1__new (sz 2) #Core.Core_arch.Arm_shared.Neon.t_uint64x2_t ()
  }
  <:
  t_KeccakState2

let shake128_squeeze_first_three_blocks
      (s: t_KeccakState2)
      (out: t_Array (t_Array u8 (sz 504)) (sz 2))
     =
  let tmp0, tmp1:(Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
      Core.Core_arch.Arm_shared.Neon.t_uint64x2_t &
    t_Array (t_Array u8 (sz 504)) (sz 2)) =
    Libcrux_sha3.Generic_keccak.squeeze_first_three_blocks (sz 2)
      #Core.Core_arch.Arm_shared.Neon.t_uint64x2_t
      (sz 168)
      (sz 504)
      s.f_state
      out
  in
  let s:t_KeccakState2 = { s with f_state = tmp0 } <: t_KeccakState2 in
  let out:t_Array (t_Array u8 (sz 504)) (sz 2) = tmp1 in
  let hax_temp_output:Prims.unit = () in
  s, out <: (t_KeccakState2 & t_Array (t_Array u8 (sz 504)) (sz 2))

let shake128_squeeze_next_block (s: t_KeccakState2) (out: t_Array (t_Array u8 (sz 168)) (sz 2)) =
  let tmp0, tmp1:(Libcrux_sha3.Generic_keccak.t_KeccakState (sz 2)
      Core.Core_arch.Arm_shared.Neon.t_uint64x2_t &
    t_Array (t_Array u8 (sz 168)) (sz 2)) =
    Libcrux_sha3.Generic_keccak.squeeze_next_block (sz 2)
      #Core.Core_arch.Arm_shared.Neon.t_uint64x2_t
      (sz 168)
      (sz 168)
      s.f_state
      out
      (sz 0)
  in
  let s:t_KeccakState2 = { s with f_state = tmp0 } <: t_KeccakState2 in
  let out:t_Array (t_Array u8 (sz 168)) (sz 2) = tmp1 in
  let hax_temp_output:Prims.unit = () in
  s, out <: (t_KeccakState2 & t_Array (t_Array u8 (sz 168)) (sz 2))
