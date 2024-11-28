module Libcrux_ml_kem.Hash_functions.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// The state.
/// It\'s only used for SHAKE128.
/// All other functions don\'t actually use any members.
val t_Simd128Hash:Type0

val v_G (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

val v_H (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val v_PRF (v_LEN: usize) (input: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

val v_PRFxN (v_K v_LEN: usize) (input: t_Array (t_Array u8 (sz 33)) v_K)
    : Prims.Pure (t_Array (t_Array u8 v_LEN) v_K) Prims.l_True (fun _ -> Prims.l_True)

val shake128_init_absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure t_Simd128Hash Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_three_blocks (v_K: usize) (st: t_Simd128Hash)
    : Prims.Pure (t_Simd128Hash & t_Array (t_Array u8 (sz 504)) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val shake128_squeeze_block (v_K: usize) (st: t_Simd128Hash)
    : Prims.Pure (t_Simd128Hash & t_Array (t_Array u8 (sz 168)) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl (v_K: usize) : Libcrux_ml_kem.Hash_functions.t_Hash t_Simd128Hash v_K
