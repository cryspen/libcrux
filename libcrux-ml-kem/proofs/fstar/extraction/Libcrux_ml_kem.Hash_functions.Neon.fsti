module Libcrux_ml_kem.Hash_functions.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// The state.
/// It's only used for SHAKE128.
/// All other functions don't actually use any members.
type t_Simd128Hash = {
  f_shake128_state:t_Array (t_Array (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64) (sz 2))
    (sz 2)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_K: usize) : Libcrux_ml_kem.Hash_functions.t_Hash t_Simd128Hash v_K =
  {
    f_G_pre = (fun (input: t_Slice u8) -> true);
    f_G_post = (fun (input: t_Slice u8) (out: t_Array u8 (sz 64)) -> true);
    f_G
    =
    (fun (input: t_Slice u8) ->
        let digest:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
        let digest:t_Array u8 (sz 64) = Libcrux_sha3.Neon.sha512 digest input in
        digest);
    f_H_pre = (fun (input: t_Slice u8) -> true);
    f_H_post = (fun (input: t_Slice u8) (out: t_Array u8 (sz 32)) -> true);
    f_H
    =
    (fun (input: t_Slice u8) ->
        let digest:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
        let digest:t_Array u8 (sz 32) = Libcrux_sha3.Neon.sha256 digest input in
        digest);
    f_PRF_pre = (fun (v_LEN: usize) (input: t_Slice u8) -> true);
    f_PRF_post = (fun (v_LEN: usize) (input: t_Slice u8) (out: t_Array u8 v_LEN) -> true);
    f_PRF
    =
    (fun (v_LEN: usize) (input: t_Slice u8) ->
        let digest:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
        let digest:t_Array u8 v_LEN = Libcrux_sha3.Neon.shake256 v_LEN digest input in
        digest);
    f_PRFxN_pre = (fun (v_LEN: usize) (input: t_Array (t_Array u8 (sz 33)) v_K) -> true);
    f_PRFxN_post
    =
    (fun
        (v_LEN: usize)
        (input: t_Array (t_Array u8 (sz 33)) v_K)
        (out: t_Array (t_Array u8 v_LEN) v_K)
        ->
        true);
    f_PRFxN
    =
    (fun (v_LEN: usize) (input: t_Array (t_Array u8 (sz 33)) v_K) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if ~.((v_K =. sz 2 <: bool) || (v_K =. sz 3 <: bool) || (v_K =. sz 4 <: bool))
              then
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: K == 2 || K == 3 || K == 4"

                    <:
                    Rust_primitives.Hax.t_Never)
            in
            ()
        in
        Libcrux_sha3.Neon.X2.shake256xN v_LEN v_K input);
    f_shake128_init_absorb_pre = (fun (input: t_Array (t_Array u8 (sz 34)) v_K) -> true);
    f_shake128_init_absorb_post
    =
    (fun (input: t_Array (t_Array u8 (sz 34)) v_K) (out: t_Simd128Hash) -> true);
    f_shake128_init_absorb
    =
    (fun (input: t_Array (t_Array u8 (sz 34)) v_K) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if ~.((v_K =. sz 2 <: bool) || (v_K =. sz 3 <: bool) || (v_K =. sz 4 <: bool))
              then
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: K == 2 || K == 3 || K == 4"

                    <:
                    Rust_primitives.Hax.t_Never)
            in
            ()
        in
        let state:t_Array (t_Array (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64) (sz 2))
          (sz 2) =
          Libcrux_sha3.Neon.X2.Incremental.shake128_absorb_finalxN v_K input
        in
        { f_shake128_state = state } <: t_Simd128Hash);
    f_shake128_squeeze_three_blocks_pre = (fun (self: t_Simd128Hash) -> true);
    f_shake128_squeeze_three_blocks_post
    =
    (fun (self: t_Simd128Hash) (out1: (t_Simd128Hash & t_Array (t_Array u8 (sz 504)) v_K)) -> true);
    f_shake128_squeeze_three_blocks
    =
    (fun (self: t_Simd128Hash) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if ~.((v_K =. sz 2 <: bool) || (v_K =. sz 3 <: bool) || (v_K =. sz 4 <: bool))
              then
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: K == 2 || K == 3 || K == 4"

                    <:
                    Rust_primitives.Hax.t_Never)
            in
            ()
        in
        let tmp0, out:(t_Array
            (t_Array (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64) (sz 2)) (sz 2) &
          t_Array (t_Array u8 (sz 504)) v_K) =
          Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze3xN (sz 504) v_K self.f_shake128_state
        in
        let self:t_Simd128Hash = { self with f_shake128_state = tmp0 } <: t_Simd128Hash in
        let hax_temp_output:t_Array (t_Array u8 (sz 504)) v_K = out in
        self, hax_temp_output <: (t_Simd128Hash & t_Array (t_Array u8 (sz 504)) v_K));
    f_shake128_squeeze_block_pre = (fun (self: t_Simd128Hash) -> true);
    f_shake128_squeeze_block_post
    =
    (fun (self: t_Simd128Hash) (out1: (t_Simd128Hash & t_Array (t_Array u8 (sz 168)) v_K)) -> true);
    f_shake128_squeeze_block
    =
    fun (self: t_Simd128Hash) ->
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            if ~.((v_K =. sz 2 <: bool) || (v_K =. sz 3 <: bool) || (v_K =. sz 4 <: bool))
            then
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: K == 2 || K == 3 || K == 4"

                  <:
                  Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let tmp0, out:(t_Array (t_Array (Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64) (sz 2))
          (sz 2) &
        t_Array (t_Array u8 (sz 168)) v_K) =
        Libcrux_sha3.Neon.X2.Incremental.shake128_squeezexN (sz 168) v_K self.f_shake128_state
      in
      let self:t_Simd128Hash = { self with f_shake128_state = tmp0 } <: t_Simd128Hash in
      let hax_temp_output:t_Array (t_Array u8 (sz 168)) v_K = out in
      self, hax_temp_output <: (t_Simd128Hash & t_Array (t_Array u8 (sz 168)) v_K)
  }
