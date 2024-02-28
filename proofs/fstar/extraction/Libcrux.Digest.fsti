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

type t_Shake128StateX2 =

type t_Shake128StateX3 =

type t_Shake128StateX4 =

val shake128_absorb_final_x2 (st: t_Shake128StateX2) (data0 data1: t_Slice u8)
    : Prims.Pure t_Shake128StateX2 Prims.l_True (fun _ -> Prims.l_True)

val shake128_absorb_final_x3 (st: t_Shake128StateX3) (data0 data1 data2: t_Slice u8)
    : Prims.Pure t_Shake128StateX3 Prims.l_True (fun _ -> Prims.l_True)

val shake128_absorb_final_x4 (st: t_Shake128StateX4) (data0 data1 data2 data3: t_Slice u8)
    : Prims.Pure t_Shake128StateX4 Prims.l_True (fun _ -> Prims.l_True)

val shake128_init_x2: Prims.unit
  -> Prims.Pure t_Shake128StateX2 Prims.l_True (fun _ -> Prims.l_True)

val shake128_init_x3: Prims.unit
  -> Prims.Pure t_Shake128StateX3 Prims.l_True (fun _ -> Prims.l_True)

val shake128_init_x4: Prims.unit
  -> Prims.Pure t_Shake128StateX4 Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_nblocks_x2 (v_OUTPUT_BYTES: usize) (st: t_Shake128StateX2)
    : Prims.Pure (t_Shake128StateX2 & t_Array (t_Array u8 v_OUTPUT_BYTES) (sz 2))
      Prims.l_True
      (fun _ -> Prims.l_True)

val shake128_squeeze_nblocks_x3 (v_OUTPUT_BYTES: usize) (st: t_Shake128StateX3)
    : Prims.Pure (t_Shake128StateX3 & t_Array (t_Array u8 v_OUTPUT_BYTES) (sz 3))
      Prims.l_True
      (fun _ -> Prims.l_True)

val shake128_squeeze_nblocks_x4 (v_OUTPUT_BYTES: usize) (st: t_Shake128StateX4)
    : Prims.Pure (t_Shake128StateX4 & t_Array (t_Array u8 v_OUTPUT_BYTES) (sz 4))
      Prims.l_True
      (fun _ -> Prims.l_True)
