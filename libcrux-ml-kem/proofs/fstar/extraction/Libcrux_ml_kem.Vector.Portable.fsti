module Libcrux_ml_kem.Vector.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable.Vector_type in
  let open Libcrux_ml_kem.Vector.Traits in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_ml_kem.Vector.Traits.t_Repr
Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector

val serialize_1_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 2))
      (requires Spec.MLKEM.serialize_pre 1 (impl.f_repr a))
      (ensures
        fun out ->
          let out:t_Array u8 (mk_usize 2) = out in
          Spec.MLKEM.serialize_pre 1 (impl.f_repr a) ==>
          Spec.MLKEM.serialize_post 1 (impl.f_repr a) out)

val deserialize_1_ (a: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 2)
      (ensures
        fun out ->
          let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = out in
          sz (Seq.length a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 a (impl.f_repr out))

val serialize_4_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 8))
      (requires Spec.MLKEM.serialize_pre 4 (impl.f_repr a))
      (ensures
        fun out ->
          let out:t_Array u8 (mk_usize 8) = out in
          Spec.MLKEM.serialize_pre 4 (impl.f_repr a) ==>
          Spec.MLKEM.serialize_post 4 (impl.f_repr a) out)

val deserialize_4_ (a: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 8)
      (ensures
        fun out ->
          let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = out in
          sz (Seq.length a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 a (impl.f_repr out))

val serialize_5_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 10)) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_5_ (a: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 10)
      (fun _ -> Prims.l_True)

val serialize_10_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 20))
      (requires Spec.MLKEM.serialize_pre 10 (impl.f_repr a))
      (ensures
        fun out ->
          let out:t_Array u8 (mk_usize 20) = out in
          Spec.MLKEM.serialize_pre 10 (impl.f_repr a) ==>
          Spec.MLKEM.serialize_post 10 (impl.f_repr a) out)

val deserialize_10_ (a: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 20)
      (ensures
        fun out ->
          let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = out in
          sz (Seq.length a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 a (impl.f_repr out))

val serialize_11_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 22)) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_11_ (a: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 22)
      (fun _ -> Prims.l_True)

val serialize_12_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 24))
      (requires Spec.MLKEM.serialize_pre 12 (impl.f_repr a))
      (ensures
        fun out ->
          let out:t_Array u8 (mk_usize 24) = out in
          Spec.MLKEM.serialize_pre 12 (impl.f_repr a) ==>
          Spec.MLKEM.serialize_post 12 (impl.f_repr a) out)

val deserialize_12_ (a: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 24)
      (ensures
        fun out ->
          let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = out in
          sz (Seq.length a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 a (impl.f_repr out))

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Libcrux_ml_kem.Vector.Traits.t_Operations
Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
