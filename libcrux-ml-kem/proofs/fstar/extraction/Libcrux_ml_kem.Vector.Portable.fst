module Libcrux_ml_kem.Vector.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable.Vector_type in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let deserialize_11_ (a: t_Slice u8) = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_11_ a

let deserialize_5_ (a: t_Slice u8) = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_5_ a

let serialize_11_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_11_ a

let serialize_5_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_5_ a

let deserialize_1_ (a: t_Slice u8) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_lemma a in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_bounded_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_ a

let deserialize_10_ (a: t_Slice u8) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_lemma a in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_bounded_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_ a

let deserialize_12_ (a: t_Slice u8) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_lemma a in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_bounded_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_ a

let deserialize_4_ (a: t_Slice u8) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_lemma a in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_bounded_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_ a

let serialize_1_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let _:Prims.unit = assert (forall i. Rust_primitives.bounded (Seq.index a.f_elements i) 1) in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.serialize_1_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_1_ a

let serialize_10_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.serialize_10_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_10_ a

let serialize_12_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.serialize_12_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_12_ a

let serialize_4_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let _:Prims.unit = assert (forall i. Rust_primitives.bounded (Seq.index a.f_elements i) 4) in
  let _:Prims.unit = Libcrux_ml_kem.Vector.Portable.Serialize.serialize_4_lemma a in
  Libcrux_ml_kem.Vector.Portable.Serialize.serialize_4_ a
