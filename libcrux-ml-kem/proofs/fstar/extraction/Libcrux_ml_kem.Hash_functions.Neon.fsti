module Libcrux_ml_kem.Hash_functions.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

/// The state.
/// It\'s only used for SHAKE128.
/// All other functions don\'t actually use any members.
val t_Simd128Hash:eqtype

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl (v_K: usize) : Libcrux_ml_kem.Hash_functions.t_Hash t_Simd128Hash v_K

val v_G (input: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 64))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 (sz 64) = result in
          result == Spec.Utils.v_G input)

val v_H (input: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 32))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          result == Spec.Utils.v_H input)

val v_PRF (v_LEN: usize) (input: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN)
      (requires v v_LEN < pow2 32)
      (ensures
        fun result ->
          let result:t_Array u8 v_LEN = result in
          result == Spec.Utils.v_PRF v_LEN input)

val v_PRFxN (v_K v_LEN: usize) (input: t_Array (t_Array u8 (sz 33)) v_K)
    : Prims.Pure (t_Array (t_Array u8 v_LEN) v_K)
      (requires v v_LEN < pow2 32 /\ (v v_K == 2 \/ v v_K == 3 \/ v v_K == 4))
      (ensures
        fun result ->
          let result:t_Array (t_Array u8 v_LEN) v_K = result in
          result == Spec.Utils.v_PRFxN v_K v_LEN input)

val shake128_init_absorb_final (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure t_Simd128Hash Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_first_three_blocks (v_K: usize) (st: t_Simd128Hash)
    : Prims.Pure (t_Simd128Hash & t_Array (t_Array u8 (sz 504)) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val shake128_squeeze_next_block (v_K: usize) (st: t_Simd128Hash)
    : Prims.Pure (t_Simd128Hash & t_Array (t_Array u8 (sz 168)) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)
