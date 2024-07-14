module Libcrux_ml_kem.Vector.Neon.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable in
  ()

val deserialize_1_ (a: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_12_ (v: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_1_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_10_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 20)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_12_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 24)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_4_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 8)) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_10_ (v: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_11_ (v: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_4_ (v: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_5_ (v: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_11_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 22)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_5_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 10)) Prims.l_True (fun _ -> Prims.l_True)
