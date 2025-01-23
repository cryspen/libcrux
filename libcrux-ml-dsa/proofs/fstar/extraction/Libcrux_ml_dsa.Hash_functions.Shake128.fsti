module Libcrux_ml_dsa.Hash_functions.Shake128
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

class t_Xof (v_Self: Type0) = {
  f_shake128_pre:t_Slice u8 -> t_Slice u8 -> Type0;
  f_shake128_post:t_Slice u8 -> t_Slice u8 -> t_Slice u8 -> Type0;
  f_shake128:x0: t_Slice u8 -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8) (f_shake128_pre x0 x1) (fun result -> f_shake128_post x0 x1 result)
}

/// When sampling matrix A we always want to do 4 absorb/squeeze calls in
/// parallel.
class t_XofX4 (v_Self: Type0) = {
  f_init_absorb_pre:t_Slice u8 -> t_Slice u8 -> t_Slice u8 -> t_Slice u8 -> Type0;
  f_init_absorb_post:t_Slice u8 -> t_Slice u8 -> t_Slice u8 -> t_Slice u8 -> v_Self -> Type0;
  f_init_absorb:x0: t_Slice u8 -> x1: t_Slice u8 -> x2: t_Slice u8 -> x3: t_Slice u8
    -> Prims.Pure v_Self
        (f_init_absorb_pre x0 x1 x2 x3)
        (fun result -> f_init_absorb_post x0 x1 x2 x3 result);
  f_squeeze_first_five_blocks_pre:
      v_Self ->
      t_Array u8 (mk_usize 840) ->
      t_Array u8 (mk_usize 840) ->
      t_Array u8 (mk_usize 840) ->
      t_Array u8 (mk_usize 840)
    -> Type0;
  f_squeeze_first_five_blocks_post:
      v_Self ->
      t_Array u8 (mk_usize 840) ->
      t_Array u8 (mk_usize 840) ->
      t_Array u8 (mk_usize 840) ->
      t_Array u8 (mk_usize 840) ->
      (v_Self & t_Array u8 (mk_usize 840) & t_Array u8 (mk_usize 840) & t_Array u8 (mk_usize 840) &
          t_Array u8 (mk_usize 840))
    -> Type0;
  f_squeeze_first_five_blocks:
      x0: v_Self ->
      x1: t_Array u8 (mk_usize 840) ->
      x2: t_Array u8 (mk_usize 840) ->
      x3: t_Array u8 (mk_usize 840) ->
      x4: t_Array u8 (mk_usize 840)
    -> Prims.Pure
        (v_Self & t_Array u8 (mk_usize 840) & t_Array u8 (mk_usize 840) & t_Array u8 (mk_usize 840) &
          t_Array u8 (mk_usize 840))
        (f_squeeze_first_five_blocks_pre x0 x1 x2 x3 x4)
        (fun result -> f_squeeze_first_five_blocks_post x0 x1 x2 x3 x4 result);
  f_squeeze_next_block_pre:v_Self -> Type0;
  f_squeeze_next_block_post:
      v_Self ->
      (v_Self &
          (t_Array u8 (mk_usize 168) & t_Array u8 (mk_usize 168) & t_Array u8 (mk_usize 168) &
            t_Array u8 (mk_usize 168)))
    -> Type0;
  f_squeeze_next_block:x0: v_Self
    -> Prims.Pure
        (v_Self &
          (t_Array u8 (mk_usize 168) & t_Array u8 (mk_usize 168) & t_Array u8 (mk_usize 168) &
            t_Array u8 (mk_usize 168)))
        (f_squeeze_next_block_pre x0)
        (fun result -> f_squeeze_next_block_post x0 result)
}

let v_BLOCK_SIZE: usize = mk_usize 168

let v_FIVE_BLOCKS_SIZE: usize = v_BLOCK_SIZE *! mk_usize 5
