module Libcrux_sha3.Traits.Internal
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// A trait for multiplexing implementations.
class t_KeccakItem (v_Self: Type0) (v_N: usize) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9442900250278684536:Core.Clone.t_Clone v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11581440318597584651:Core.Marker.t_Copy v_Self;
  f_zero_pre:Prims.unit -> bool;
  f_zero_post:Prims.unit -> v_Self -> bool;
  f_zero:x0: Prims.unit -> Prims.Pure v_Self (f_zero_pre x0) (fun result -> f_zero_post x0 result);
  f_xor5_pre:v_Self -> v_Self -> v_Self -> v_Self -> v_Self -> bool;
  f_xor5_post:v_Self -> v_Self -> v_Self -> v_Self -> v_Self -> v_Self -> bool;
  f_xor5:x0: v_Self -> x1: v_Self -> x2: v_Self -> x3: v_Self -> x4: v_Self
    -> Prims.Pure v_Self
        (f_xor5_pre x0 x1 x2 x3 x4)
        (fun result -> f_xor5_post x0 x1 x2 x3 x4 result);
  f_rotate_left1_and_xor_pre:v_Self -> v_Self -> bool;
  f_rotate_left1_and_xor_post:v_Self -> v_Self -> v_Self -> bool;
  f_rotate_left1_and_xor:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_rotate_left1_and_xor_pre x0 x1)
        (fun result -> f_rotate_left1_and_xor_post x0 x1 result);
  f_xor_and_rotate_pre:v_LEFT: i32 -> v_RIGHT: i32 -> v_Self -> v_Self -> bool;
  f_xor_and_rotate_post:v_LEFT: i32 -> v_RIGHT: i32 -> v_Self -> v_Self -> v_Self -> bool;
  f_xor_and_rotate:v_LEFT: i32 -> v_RIGHT: i32 -> x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_xor_and_rotate_pre v_LEFT v_RIGHT x0 x1)
        (fun result -> f_xor_and_rotate_post v_LEFT v_RIGHT x0 x1 result);
  f_and_not_xor_pre:v_Self -> v_Self -> v_Self -> bool;
  f_and_not_xor_post:v_Self -> v_Self -> v_Self -> v_Self -> bool;
  f_and_not_xor:x0: v_Self -> x1: v_Self -> x2: v_Self
    -> Prims.Pure v_Self
        (f_and_not_xor_pre x0 x1 x2)
        (fun result -> f_and_not_xor_post x0 x1 x2 result);
  f_xor_constant_pre:v_Self -> u64 -> bool;
  f_xor_constant_post:v_Self -> u64 -> v_Self -> bool;
  f_xor_constant:x0: v_Self -> x1: u64
    -> Prims.Pure v_Self (f_xor_constant_pre x0 x1) (fun result -> f_xor_constant_post x0 x1 result);
  f_xor_pre:v_Self -> v_Self -> bool;
  f_xor_post:v_Self -> v_Self -> v_Self -> bool;
  f_xor:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_xor_pre x0 x1) (fun result -> f_xor_post x0 x1 result);
  f_load_block_pre:
      v_BLOCKSIZE: usize ->
      t_Array (t_Array v_Self (sz 5)) (sz 5) ->
      t_Array (t_Slice u8) v_N
    -> bool;
  f_load_block_post:
      v_BLOCKSIZE: usize ->
      t_Array (t_Array v_Self (sz 5)) (sz 5) ->
      t_Array (t_Slice u8) v_N ->
      t_Array (t_Array v_Self (sz 5)) (sz 5)
    -> bool;
  f_load_block:
      v_BLOCKSIZE: usize ->
      x0: t_Array (t_Array v_Self (sz 5)) (sz 5) ->
      x1: t_Array (t_Slice u8) v_N
    -> Prims.Pure (t_Array (t_Array v_Self (sz 5)) (sz 5))
        (f_load_block_pre v_BLOCKSIZE x0 x1)
        (fun result -> f_load_block_post v_BLOCKSIZE x0 x1 result);
  f_store_block_pre:
      v_BLOCKSIZE: usize ->
      v_SIZE: usize ->
      t_Array (t_Array v_Self (sz 5)) (sz 5) ->
      t_Array (t_Array u8 v_SIZE) v_N ->
      usize
    -> bool;
  f_store_block_post:
      v_BLOCKSIZE: usize ->
      v_SIZE: usize ->
      t_Array (t_Array v_Self (sz 5)) (sz 5) ->
      t_Array (t_Array u8 v_SIZE) v_N ->
      usize ->
      t_Array (t_Array u8 v_SIZE) v_N
    -> bool;
  f_store_block:
      v_BLOCKSIZE: usize ->
      v_SIZE: usize ->
      x0: t_Array (t_Array v_Self (sz 5)) (sz 5) ->
      x1: t_Array (t_Array u8 v_SIZE) v_N ->
      x2: usize
    -> Prims.Pure (t_Array (t_Array u8 v_SIZE) v_N)
        (f_store_block_pre v_BLOCKSIZE v_SIZE x0 x1 x2)
        (fun result -> f_store_block_post v_BLOCKSIZE v_SIZE x0 x1 x2 result);
  f_load_block_full_pre:
      v_BLOCKSIZE: usize ->
      t_Array (t_Array v_Self (sz 5)) (sz 5) ->
      t_Array (t_Array u8 (sz 200)) v_N
    -> bool;
  f_load_block_full_post:
      v_BLOCKSIZE: usize ->
      t_Array (t_Array v_Self (sz 5)) (sz 5) ->
      t_Array (t_Array u8 (sz 200)) v_N ->
      t_Array (t_Array v_Self (sz 5)) (sz 5)
    -> bool;
  f_load_block_full:
      v_BLOCKSIZE: usize ->
      x0: t_Array (t_Array v_Self (sz 5)) (sz 5) ->
      x1: t_Array (t_Array u8 (sz 200)) v_N
    -> Prims.Pure (t_Array (t_Array v_Self (sz 5)) (sz 5))
        (f_load_block_full_pre v_BLOCKSIZE x0 x1)
        (fun result -> f_load_block_full_post v_BLOCKSIZE x0 x1 result);
  f_store_block_full_pre:v_BLOCKSIZE: usize -> t_Array (t_Array v_Self (sz 5)) (sz 5) -> bool;
  f_store_block_full_post:
      v_BLOCKSIZE: usize ->
      t_Array (t_Array v_Self (sz 5)) (sz 5) ->
      t_Array (t_Array u8 (sz 200)) v_N
    -> bool;
  f_store_block_full:v_BLOCKSIZE: usize -> x0: t_Array (t_Array v_Self (sz 5)) (sz 5)
    -> Prims.Pure (t_Array (t_Array u8 (sz 200)) v_N)
        (f_store_block_full_pre v_BLOCKSIZE x0)
        (fun result -> f_store_block_full_post v_BLOCKSIZE x0 result);
  f_slice_n_pre:t_Array (t_Slice u8) v_N -> usize -> usize -> bool;
  f_slice_n_post:t_Array (t_Slice u8) v_N -> usize -> usize -> t_Array (t_Slice u8) v_N -> bool;
  f_slice_n:x0: t_Array (t_Slice u8) v_N -> x1: usize -> x2: usize
    -> Prims.Pure (t_Array (t_Slice u8) v_N)
        (f_slice_n_pre x0 x1 x2)
        (fun result -> f_slice_n_post x0 x1 x2 result)
}
