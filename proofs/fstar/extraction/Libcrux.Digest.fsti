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

type t_Shake128State


val shake128_absorb_final (st: t_Shake128State) (data: t_Slice u8)
    : Prims.Pure t_Shake128State Prims.l_True (fun _ -> Prims.l_True)

val shake128_init: Prims.unit -> Prims.Pure t_Shake128State Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_nblocks (v_OUTPUT_BYTES: usize) (st: t_Shake128State)
    : Prims.Pure (t_Shake128State & t_Array u8 v_OUTPUT_BYTES) Prims.l_True (fun _ -> Prims.l_True)
