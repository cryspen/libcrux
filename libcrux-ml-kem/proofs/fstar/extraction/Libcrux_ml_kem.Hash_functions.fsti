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
  f_G_pre:input: t_Slice u8 -> pred: Type0{true ==> pred};
  f_G_post:input: t_Slice u8 -> result: t_Array u8 (sz 64)
    -> pred: Type0{pred ==> result == Spec.Utils.v_G input};
  f_G:x0: t_Slice u8
    -> Prims.Pure (t_Array u8 (sz 64)) (f_G_pre x0) (fun result -> f_G_post x0 result);
  f_H_pre:input: t_Slice u8 -> pred: Type0{true ==> pred};
  f_H_post:input: t_Slice u8 -> result: t_Array u8 (sz 32)
    -> pred: Type0{pred ==> result == Spec.Utils.v_H input};
  f_H:x0: t_Slice u8
    -> Prims.Pure (t_Array u8 (sz 32)) (f_H_pre x0) (fun result -> f_H_post x0 result);
  f_PRF_pre:v_LEN: usize -> input: t_Slice u8 -> pred: Type0{v v_LEN < pow2 32 ==> pred};
  f_PRF_post:v_LEN: usize -> input: t_Slice u8 -> result: t_Array u8 v_LEN
    -> pred: Type0{pred ==> v v_LEN < pow2 32 ==> result == Spec.Utils.v_PRF v_LEN input};
  f_PRF:v_LEN: usize -> x0: t_Slice u8
    -> Prims.Pure (t_Array u8 v_LEN) (f_PRF_pre v_LEN x0) (fun result -> f_PRF_post v_LEN x0 result);
  f_PRFxN_pre:v_LEN: usize -> input: t_Array (t_Array u8 (sz 33)) v_K
    -> pred: Type0{v v_LEN < pow2 32 /\ (v v_K == 2 \/ v v_K == 3 \/ v v_K == 4) ==> pred};
  f_PRFxN_post:
      v_LEN: usize ->
      input: t_Array (t_Array u8 (sz 33)) v_K ->
      result: t_Array (t_Array u8 v_LEN) v_K
    -> pred:
      Type0
        { pred ==>
          (v v_LEN < pow2 32 /\ (v v_K == 2 \/ v v_K == 3 \/ v v_K == 4)) ==>
          result == Spec.Utils.v_PRFxN v_K v_LEN input };
  f_PRFxN:v_LEN: usize -> x0: t_Array (t_Array u8 (sz 33)) v_K
    -> Prims.Pure (t_Array (t_Array u8 v_LEN) v_K)
        (f_PRFxN_pre v_LEN x0)
        (fun result -> f_PRFxN_post v_LEN x0 result);
  f_shake128_init_absorb_final_pre:input: t_Array (t_Array u8 (sz 34)) v_K
    -> pred: Type0{true ==> pred};
  f_shake128_init_absorb_final_post:t_Array (t_Array u8 (sz 34)) v_K -> v_Self -> Type0;
  f_shake128_init_absorb_final:x0: t_Array (t_Array u8 (sz 34)) v_K
    -> Prims.Pure v_Self
        (f_shake128_init_absorb_final_pre x0)
        (fun result -> f_shake128_init_absorb_final_post x0 result);
  f_shake128_squeeze_first_three_blocks_pre:self___: v_Self -> pred: Type0{true ==> pred};
  f_shake128_squeeze_first_three_blocks_post:v_Self -> (v_Self & t_Array (t_Array u8 (sz 504)) v_K)
    -> Type0;
  f_shake128_squeeze_first_three_blocks:x0: v_Self
    -> Prims.Pure (v_Self & t_Array (t_Array u8 (sz 504)) v_K)
        (f_shake128_squeeze_first_three_blocks_pre x0)
        (fun result -> f_shake128_squeeze_first_three_blocks_post x0 result);
  f_shake128_squeeze_next_block_pre:self___: v_Self -> pred: Type0{true ==> pred};
  f_shake128_squeeze_next_block_post:v_Self -> (v_Self & t_Array (t_Array u8 (sz 168)) v_K) -> Type0;
  f_shake128_squeeze_next_block:x0: v_Self
    -> Prims.Pure (v_Self & t_Array (t_Array u8 (sz 168)) v_K)
        (f_shake128_squeeze_next_block_pre x0)
        (fun result -> f_shake128_squeeze_next_block_post x0 result)
}

/// The SHA3 block size.
let v_BLOCK_SIZE: usize = sz 168

/// The size of 3 SHA3 blocks.
let v_THREE_BLOCKS: usize = v_BLOCK_SIZE *! sz 3
