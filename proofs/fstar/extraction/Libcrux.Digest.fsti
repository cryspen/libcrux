module Libcrux.Digest
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val sha3_256_ (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val sha3_512_ (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

/// SHAKE 256
/// The caller must define the size of the output in the return type.
val shake256 (v_LEN: usize) (data: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)
