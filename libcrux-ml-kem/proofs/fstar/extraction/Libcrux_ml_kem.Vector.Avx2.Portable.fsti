module Libcrux_ml_kem.Vector.Avx2.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val deserialize_11_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_11_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

type t_PortableVector = { f_elements:t_Array i16 (sz 16) }

val from_i16_array (array: t_Array i16 (sz 16))
    : Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

val serialize_11_ (v: t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 22)) Prims.l_True (fun _ -> Prims.l_True)

val to_i16_array (v: t_PortableVector)
    : Prims.Pure (t_Array i16 (sz 16)) Prims.l_True (fun _ -> Prims.l_True)

val zero: Prims.unit -> Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_11_ (bytes: t_Slice u8)
    : Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)
