module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val v_G (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

val v_H (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val v_PRF (v_LEN: usize) (input: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

val v_XOF_absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure (t_Array Libcrux.Digest.t_Shake128State v_K) Prims.l_True (fun _ -> Prims.l_True)

val v_XOF_free (v_K: usize) (xof_state: t_Array Libcrux.Digest.t_Shake128State v_K)
    : Prims.Pure (t_Array Libcrux.Digest.t_Shake128State v_K) Prims.l_True (fun _ -> Prims.l_True)

val v_XOF_squeeze_block (v_K: usize) (xof_state: t_Array Libcrux.Digest.t_Shake128State v_K)
    : Prims.Pure (t_Array (t_Array u8 (sz 168)) v_K & t_Array Libcrux.Digest.t_Shake128State v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val v_XOF_squeeze_three_blocks (v_K: usize) (xof_state: t_Array Libcrux.Digest.t_Shake128State v_K)
    : Prims.Pure (t_Array (t_Array u8 (sz 504)) v_K & t_Array Libcrux.Digest.t_Shake128State v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)
