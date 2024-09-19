module Libcrux_ml_kem.Vector.Avx2.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable in
  ()

val deserialize_1_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize_10_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize_12_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize_4_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. sz 8)
      (fun _ -> Prims.l_True)

val deserialize_5_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val serialize_1_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_10_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (sz 20)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_12_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (sz 24)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_5_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (sz 10)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_4_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (sz 8))
      (requires BitVec.Intrinsics.forall_bool #256 (fun i -> i % 16 < 4 || vector i = 0))
      (fun _ -> Prims.l_True)

val deserialize_11_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val serialize_11_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (sz 22)) Prims.l_True (fun _ -> Prims.l_True)
