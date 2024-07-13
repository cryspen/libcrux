module Libcrux_ml_kem.Hash_functions.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val v_G (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

val v_H (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val v_PRF (v_LEN: usize) (input: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

val v_PRFxN (v_K v_LEN: usize) (input: t_Array (t_Array u8 (sz 33)) v_K)
    : Prims.Pure (t_Array (t_Array u8 v_LEN) v_K) Prims.l_True (fun _ -> Prims.l_True)

/// The state.
/// It\'s only used for SHAKE128.
/// All other functions don\'t actually use any members.
val t_Simd256Hash:Type0

val shake128_init_absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure t_Simd256Hash Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_block (v_K: usize) (st: t_Simd256Hash)
    : Prims.Pure (t_Simd256Hash & t_Array (t_Array u8 (sz 168)) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val shake128_squeeze_three_blocks (v_K: usize) (st: t_Simd256Hash)
    : Prims.Pure (t_Simd256Hash & t_Array (t_Array u8 (sz 504)) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_K: usize) : Libcrux_ml_kem.Hash_functions.t_Hash t_Simd256Hash v_K =
  {
    f_G_pre = (fun (input: t_Slice u8) -> true);
    f_G_post = (fun (input: t_Slice u8) (out: t_Array u8 (sz 64)) -> true);
    f_G = (fun (input: t_Slice u8) -> v_G input);
    f_H_pre = (fun (input: t_Slice u8) -> true);
    f_H_post = (fun (input: t_Slice u8) (out: t_Array u8 (sz 32)) -> true);
    f_H = (fun (input: t_Slice u8) -> v_H input);
    f_PRF_pre = (fun (v_LEN: usize) (input: t_Slice u8) -> true);
    f_PRF_post = (fun (v_LEN: usize) (input: t_Slice u8) (out: t_Array u8 v_LEN) -> true);
    f_PRF = (fun (v_LEN: usize) (input: t_Slice u8) -> v_PRF v_LEN input);
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
    (fun (v_LEN: usize) (input: t_Array (t_Array u8 (sz 33)) v_K) -> v_PRFxN v_K v_LEN input);
    f_shake128_init_absorb_pre = (fun (input: t_Array (t_Array u8 (sz 34)) v_K) -> true);
    f_shake128_init_absorb_post
    =
    (fun (input: t_Array (t_Array u8 (sz 34)) v_K) (out: t_Simd256Hash) -> true);
    f_shake128_init_absorb
    =
    (fun (input: t_Array (t_Array u8 (sz 34)) v_K) -> shake128_init_absorb v_K input);
    f_shake128_squeeze_three_blocks_pre = (fun (self: t_Simd256Hash) -> true);
    f_shake128_squeeze_three_blocks_post
    =
    (fun (self: t_Simd256Hash) (out1: (t_Simd256Hash & t_Array (t_Array u8 (sz 504)) v_K)) -> true);
    f_shake128_squeeze_three_blocks
    =
    (fun (self: t_Simd256Hash) ->
        let tmp0, out:(t_Simd256Hash & t_Array (t_Array u8 (sz 504)) v_K) =
          shake128_squeeze_three_blocks v_K self
        in
        let self:t_Simd256Hash = tmp0 in
        let hax_temp_output:t_Array (t_Array u8 (sz 504)) v_K = out in
        self, hax_temp_output <: (t_Simd256Hash & t_Array (t_Array u8 (sz 504)) v_K));
    f_shake128_squeeze_block_pre = (fun (self: t_Simd256Hash) -> true);
    f_shake128_squeeze_block_post
    =
    (fun (self: t_Simd256Hash) (out1: (t_Simd256Hash & t_Array (t_Array u8 (sz 168)) v_K)) -> true);
    f_shake128_squeeze_block
    =
    fun (self: t_Simd256Hash) ->
      let tmp0, out:(t_Simd256Hash & t_Array (t_Array u8 (sz 168)) v_K) =
        shake128_squeeze_block v_K self
      in
      let self:t_Simd256Hash = tmp0 in
      let hax_temp_output:t_Array (t_Array u8 (sz 168)) v_K = out in
      self, hax_temp_output <: (t_Simd256Hash & t_Array (t_Array u8 (sz 168)) v_K)
  }
