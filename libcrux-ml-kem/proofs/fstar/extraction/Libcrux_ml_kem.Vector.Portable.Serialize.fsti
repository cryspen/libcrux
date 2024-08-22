module Libcrux_ml_kem.Vector.Portable.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val deserialize_10_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_11_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_12_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_4_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_5_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_10_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize_11_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_12_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize_4_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize_5_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize_1_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_10_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 20)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_11_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 22)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_12_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 24)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_4_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 8)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_5_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 10)) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_1_ (v: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_10_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_11_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_12_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_4_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_5_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)
