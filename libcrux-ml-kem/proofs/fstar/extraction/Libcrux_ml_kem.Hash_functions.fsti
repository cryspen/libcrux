module Libcrux_ml_kem.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Abstraction for the hashing, to pick the fastest version depending on the
/// platform features available.
/// There are 3 instantiations of this trait right now, using the libcrux-sha3 crate.
/// - AVX2
/// - NEON
/// - Portable
class t_Hash (v_Self: Type0) (v_K: usize) = {
  f_G_pre:t_Slice u8 -> Type0;
  f_G_post:t_Slice u8 -> t_Array u8 (sz 64) -> Type0;
  f_G:x0: t_Slice u8
    -> Prims.Pure (t_Array u8 (sz 64)) (f_G_pre x0) (fun result -> f_G_post x0 result);
  f_H_pre:t_Slice u8 -> Type0;
  f_H_post:t_Slice u8 -> t_Array u8 (sz 32) -> Type0;
  f_H:x0: t_Slice u8
    -> Prims.Pure (t_Array u8 (sz 32)) (f_H_pre x0) (fun result -> f_H_post x0 result);
  f_PRF_pre:v_LEN: usize -> t_Slice u8 -> Type0;
  f_PRF_post:v_LEN: usize -> t_Slice u8 -> t_Array u8 v_LEN -> Type0;
  f_PRF:v_LEN: usize -> x0: t_Slice u8
    -> Prims.Pure (t_Array u8 v_LEN) (f_PRF_pre v_LEN x0) (fun result -> f_PRF_post v_LEN x0 result);
  f_PRFxN_pre:v_LEN: usize -> t_Array (t_Array u8 (sz 33)) v_K -> Type0;
  f_PRFxN_post:v_LEN: usize -> t_Array (t_Array u8 (sz 33)) v_K -> t_Array (t_Array u8 v_LEN) v_K
    -> Type0;
  f_PRFxN:v_LEN: usize -> x0: t_Array (t_Array u8 (sz 33)) v_K
    -> Prims.Pure (t_Array (t_Array u8 v_LEN) v_K)
        (f_PRFxN_pre v_LEN x0)
        (fun result -> f_PRFxN_post v_LEN x0 result);
  f_shake128_init_absorb_pre:t_Array (t_Array u8 (sz 34)) v_K -> Type0;
  f_shake128_init_absorb_post:t_Array (t_Array u8 (sz 34)) v_K -> v_Self -> Type0;
  f_shake128_init_absorb:x0: t_Array (t_Array u8 (sz 34)) v_K
    -> Prims.Pure v_Self
        (f_shake128_init_absorb_pre x0)
        (fun result -> f_shake128_init_absorb_post x0 result);
  f_shake128_squeeze_three_blocks_pre:v_Self -> Type0;
  f_shake128_squeeze_three_blocks_post:v_Self -> (v_Self & t_Array (t_Array u8 (sz 504)) v_K)
    -> Type0;
  f_shake128_squeeze_three_blocks:x0: v_Self
    -> Prims.Pure (v_Self & t_Array (t_Array u8 (sz 504)) v_K)
        (f_shake128_squeeze_three_blocks_pre x0)
        (fun result -> f_shake128_squeeze_three_blocks_post x0 result);
  f_shake128_squeeze_block_pre:v_Self -> Type0;
  f_shake128_squeeze_block_post:v_Self -> (v_Self & t_Array (t_Array u8 (sz 168)) v_K) -> Type0;
  f_shake128_squeeze_block:x0: v_Self
    -> Prims.Pure (v_Self & t_Array (t_Array u8 (sz 168)) v_K)
        (f_shake128_squeeze_block_pre x0)
        (fun result -> f_shake128_squeeze_block_post x0 result)
}

/// The SHA3 block size.
let v_BLOCK_SIZE: usize = sz 168

/// The size of 3 SHA3 blocks.
let v_THREE_BLOCKS: usize = v_BLOCK_SIZE *! sz 3
