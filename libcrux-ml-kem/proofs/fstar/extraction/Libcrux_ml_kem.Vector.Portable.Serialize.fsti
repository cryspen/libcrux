module Libcrux_ml_kem.Vector.Portable.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int in
  ()

val serialize_1_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 2)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_1_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 1)) 
  (ensures bit_vec_of_int_t_array (serialize_1_ inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 1)

val deserialize_1_ (v: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 v <: usize) =. mk_usize 2)
      (fun _ -> Prims.l_True)

val deserialize_1_lemma (inputs: t_Array u8 (sz 2)) : Lemma
  (ensures bit_vec_of_int_t_array (deserialize_1_ inputs).f_elements 1 == bit_vec_of_int_t_array inputs 8)

val deserialize_1_bounded_lemma (inputs: t_Array u8 (sz 2)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (deserialize_1_ inputs).f_elements i) 1)

val serialize_4_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8)
      (requires (Core.Slice.impl__len #i16 v <: usize) =. mk_usize 8)
      (fun _ -> Prims.l_True)

val serialize_4_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 8)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_4_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 4)) 
  (ensures bit_vec_of_int_t_array (serialize_4_ inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 4)

val deserialize_4_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 4)
      (fun _ -> Prims.l_True)

val deserialize_4_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 8)
      (fun _ -> Prims.l_True)

val deserialize_4_bounded_lemma (inputs: t_Array u8 (sz 8)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (deserialize_4_ inputs).f_elements i) 4)

val deserialize_4_lemma (inputs: t_Array u8 (sz 8)) : Lemma
  (ensures bit_vec_of_int_t_array (deserialize_4_ inputs).f_elements 4 == bit_vec_of_int_t_array inputs 8)

val serialize_5_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8)
      (requires (Core.Slice.impl__len #i16 v <: usize) =. mk_usize 8)
      (fun _ -> Prims.l_True)

val serialize_5_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 10)) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_5_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 5)
      (fun _ -> Prims.l_True)

val deserialize_5_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 10)
      (fun _ -> Prims.l_True)

val serialize_10_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8)
      (requires (Core.Slice.impl__len #i16 v <: usize) =. mk_usize 4)
      (fun _ -> Prims.l_True)

val serialize_10_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 20)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_10_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 10)) 
  (ensures bit_vec_of_int_t_array (serialize_10_ inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 10)

val deserialize_10_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 10)
      (fun _ -> Prims.l_True)

val deserialize_10_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 20)
      (fun _ -> Prims.l_True)

val deserialize_10_lemma (inputs: t_Array u8 (sz 20)) : Lemma
  (ensures bit_vec_of_int_t_array (deserialize_10_ inputs).f_elements 10 == bit_vec_of_int_t_array inputs 8)

val deserialize_10_bounded_lemma (inputs: t_Array u8 (sz 20)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (deserialize_10_ inputs).f_elements i) 10)

val serialize_11_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
      (requires (Core.Slice.impl__len #i16 v <: usize) =. mk_usize 8)
      (fun _ -> Prims.l_True)

val serialize_11_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 22)) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_11_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 11)
      (fun _ -> Prims.l_True)

val deserialize_11_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 22)
      (fun _ -> Prims.l_True)

val serialize_12_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8)
      (requires (Core.Slice.impl__len #i16 v <: usize) =. mk_usize 2)
      (fun _ -> Prims.l_True)

val serialize_12_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Array u8 (mk_usize 24)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_12_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 12)) 
  (ensures bit_vec_of_int_t_array (serialize_12_ inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 12)

val deserialize_12_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16)
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 3)
      (fun _ -> Prims.l_True)

val deserialize_12_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 24)
      (fun _ -> Prims.l_True)

val deserialize_12_bounded_lemma (inputs: t_Array u8 (sz 24)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (deserialize_12_ inputs).f_elements i) 12)

val deserialize_12_lemma (inputs: t_Array u8 (sz 24)) : Lemma
  (ensures bit_vec_of_int_t_array (deserialize_12_ inputs).f_elements 12 == bit_vec_of_int_t_array inputs 8)
