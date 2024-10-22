module Libcrux_ml_dsa.Hash_functions.Shake256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

class t_Xof (v_Self: Type0) = {
  f_shake256_pre:v_OUTPUT_LENGTH: usize -> t_Slice u8 -> t_Array u8 v_OUTPUT_LENGTH -> Type0;
  f_shake256_post:
      v_OUTPUT_LENGTH: usize ->
      t_Slice u8 ->
      t_Array u8 v_OUTPUT_LENGTH ->
      t_Array u8 v_OUTPUT_LENGTH
    -> Type0;
  f_shake256:v_OUTPUT_LENGTH: usize -> x0: t_Slice u8 -> x1: t_Array u8 v_OUTPUT_LENGTH
    -> Prims.Pure (t_Array u8 v_OUTPUT_LENGTH)
        (f_shake256_pre v_OUTPUT_LENGTH x0 x1)
        (fun result -> f_shake256_post v_OUTPUT_LENGTH x0 x1 result);
  f_init_absorb_pre:t_Slice u8 -> Type0;
  f_init_absorb_post:t_Slice u8 -> v_Self -> Type0;
  f_init_absorb:x0: t_Slice u8
    -> Prims.Pure v_Self (f_init_absorb_pre x0) (fun result -> f_init_absorb_post x0 result);
  f_squeeze_first_block_pre:v_Self -> Type0;
  f_squeeze_first_block_post:v_Self -> (v_Self & t_Array u8 (sz 136)) -> Type0;
  f_squeeze_first_block:x0: v_Self
    -> Prims.Pure (v_Self & t_Array u8 (sz 136))
        (f_squeeze_first_block_pre x0)
        (fun result -> f_squeeze_first_block_post x0 result);
  f_squeeze_next_block_pre:v_Self -> Type0;
  f_squeeze_next_block_post:v_Self -> (v_Self & t_Array u8 (sz 136)) -> Type0;
  f_squeeze_next_block:x0: v_Self
    -> Prims.Pure (v_Self & t_Array u8 (sz 136))
        (f_squeeze_next_block_pre x0)
        (fun result -> f_squeeze_next_block_post x0 result)
}

class t_XofX4 (v_Self: Type0) = {
  f_init_absorb_x4_pre:t_Slice u8 -> t_Slice u8 -> t_Slice u8 -> t_Slice u8 -> Type0;
  f_init_absorb_x4_post:t_Slice u8 -> t_Slice u8 -> t_Slice u8 -> t_Slice u8 -> v_Self -> Type0;
  f_init_absorb_x4:x0: t_Slice u8 -> x1: t_Slice u8 -> x2: t_Slice u8 -> x3: t_Slice u8
    -> Prims.Pure v_Self
        (f_init_absorb_x4_pre x0 x1 x2 x3)
        (fun result -> f_init_absorb_x4_post x0 x1 x2 x3 result);
  f_squeeze_first_block_x4_pre:v_Self -> Type0;
  f_squeeze_first_block_x4_post:
      v_Self ->
      (v_Self &
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
    -> Type0;
  f_squeeze_first_block_x4:x0: v_Self
    -> Prims.Pure
        (v_Self &
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
        (f_squeeze_first_block_x4_pre x0)
        (fun result -> f_squeeze_first_block_x4_post x0 result);
  f_squeeze_next_block_x4_pre:v_Self -> Type0;
  f_squeeze_next_block_x4_post:
      v_Self ->
      (v_Self &
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
    -> Type0;
  f_squeeze_next_block_x4:x0: v_Self
    -> Prims.Pure
        (v_Self &
          (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
        (f_squeeze_next_block_x4_pre x0)
        (fun result -> f_squeeze_next_block_x4_post x0 result);
  f_shake256_x4_pre:
      v_OUT_LEN: usize ->
      t_Slice u8 ->
      t_Slice u8 ->
      t_Slice u8 ->
      t_Slice u8 ->
      t_Array u8 v_OUT_LEN ->
      t_Array u8 v_OUT_LEN ->
      t_Array u8 v_OUT_LEN ->
      t_Array u8 v_OUT_LEN
    -> Type0;
  f_shake256_x4_post:
      v_OUT_LEN: usize ->
      t_Slice u8 ->
      t_Slice u8 ->
      t_Slice u8 ->
      t_Slice u8 ->
      t_Array u8 v_OUT_LEN ->
      t_Array u8 v_OUT_LEN ->
      t_Array u8 v_OUT_LEN ->
      t_Array u8 v_OUT_LEN ->
      (t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN)
    -> Type0;
  f_shake256_x4:
      v_OUT_LEN: usize ->
      x0: t_Slice u8 ->
      x1: t_Slice u8 ->
      x2: t_Slice u8 ->
      x3: t_Slice u8 ->
      x4: t_Array u8 v_OUT_LEN ->
      x5: t_Array u8 v_OUT_LEN ->
      x6: t_Array u8 v_OUT_LEN ->
      x7: t_Array u8 v_OUT_LEN
    -> Prims.Pure
        (t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN & t_Array u8 v_OUT_LEN)
        (f_shake256_x4_pre v_OUT_LEN x0 x1 x2 x3 x4 x5 x6 x7)
        (fun result -> f_shake256_x4_post v_OUT_LEN x0 x1 x2 x3 x4 x5 x6 x7 result)
}

let v_BLOCK_SIZE: usize = sz 136
