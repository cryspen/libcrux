module Libcrux.Digest
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val sha3_256_ (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val sha3_512_ (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

val shake256 (v_LEN: usize) (data: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

val t_Shake128State:Type

val impl__Shake128State__new: v_K: usize -> Prims.unit
  -> Prims.Pure (t_Array t_Shake128State v_K) Prims.l_True (fun _ -> Prims.l_True)

val shake128_absorb_final
      (v_K: usize)
      (st: t_Array t_Shake128State v_K)
      (data: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure (t_Array t_Shake128State v_K) Prims.l_True (fun _ -> Prims.l_True)

val shake128_free (v_K: usize) (state: t_Array t_Shake128State v_K)
    : Prims.Pure (t_Array t_Shake128State v_K) Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_nblocks (v_OUTPUT_BYTES v_K: usize) (st: t_Array t_Shake128State v_K)
    : Prims.Pure (t_Array t_Shake128State v_K & t_Array (t_Array u8 v_OUTPUT_BYTES) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)
