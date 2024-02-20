module Libcrux.Digest
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val shake128x4_256_ (v_LEN: usize) (data0 data1 data2 data3: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sha3_256_ (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val sha3_512_ (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

val shake128 (v_LEN: usize) (data: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

val shake256 (v_LEN: usize) (data: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

val shake128x4_portable (v_LEN: usize) (data0 data1 data2 data3: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN)
      Prims.l_True
      (fun _ -> Prims.l_True)

val shake128x4 (v_LEN: usize) (data0 data1 data2 data3: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN)
      Prims.l_True
      (fun _ -> Prims.l_True)
