module Libcrux_ml_kem.Vector.Avx2.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

val serialize_1_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (mk_usize 2))
      (requires forall i. i % 16 >= 1 ==> vector i == 0)
      (ensures
        fun result ->
          let result:t_Array u8 (mk_usize 2) = result in
          forall i. bit_vec_of_int_t_array result 8 i == vector (i * 16))

val deserialize_1___deserialize_1_i16s (a b: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      Prims.l_True
      (ensures
        fun coefficients ->
          let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 = coefficients in
          forall (i: nat{i < 256}).
            coefficients i =
            (if i % 16 >= 1
              then 0
              else
                let j = (i / 16) * 1 + i % 16 in
                if i < 128 then get_bit a (sz j) else get_bit b (sz (j - 8))))

val deserialize_1___deserialize_1_u8s (a b: u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      Prims.l_True
      (ensures
        fun coefficients ->
          let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 = coefficients in
          forall (i: nat{i < 256}).
            coefficients i =
            (if i % 16 >= 1
              then 0
              else
                let j = (i / 16) * 1 + i % 16 in
                if i < 128 then get_bit a (sz j) else get_bit b (sz (j - 8))))

val deserialize_1_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 2)
      (ensures
        fun coefficients ->
          let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 = coefficients in
          forall (i: nat{i < 256}).
            coefficients i =
            (if i % 16 >= 1
              then 0
              else
                let j = (i / 16) * 1 + i % 16 in
                bit_vec_of_int_t_array (bytes <: t_Array _ (sz 2)) 8 j))

include BitVec.Intrinsics {mm256_concat_pairs_n}

val serialize_4_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (mk_usize 8))
      (requires forall (i: nat{i < 256}). i % 16 < 4 || vector i = 0)
      (ensures
        fun r ->
          let r:t_Array u8 (mk_usize 8) = r in
          forall (i: nat{i < 64}). bit_vec_of_int_t_array r 8 i == vector ((i / 4) * 16 + i % 4))

val deserialize_4___deserialize_4_i16s (b0 b1 b2 b3 b4 b5 b6 b7: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      Prims.l_True
      (ensures
        fun coefficients ->
          let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 = coefficients in
          forall (i: nat{i < 256}).
            coefficients i =
            (if i % 16 < 4
              then
                let j = (i / 16) * 4 + i % 16 in
                (match i / 32 with
                  | 0 -> get_bit b0 (sz j)
                  | 1 -> get_bit b1 (sz (j - 8))
                  | 2 -> get_bit b2 (sz (j - 16))
                  | 3 -> get_bit b3 (sz (j - 24))
                  | 4 -> get_bit b4 (sz (j - 32))
                  | 5 -> get_bit b5 (sz (j - 40))
                  | 6 -> get_bit b6 (sz (j - 48))
                  | 7 -> get_bit b7 (sz (j - 56)))
              else 0))

val deserialize_4___deserialize_4_u8s (b0 b1 b2 b3 b4 b5 b6 b7: u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      Prims.l_True
      (ensures
        fun coefficients ->
          let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 = coefficients in
          forall (i: nat{i < 256}).
            coefficients i =
            (if i % 16 < 4
              then
                let j = (i / 16) * 4 + i % 16 in
                (match i / 32 with
                  | 0 -> get_bit b0 (sz j)
                  | 1 -> get_bit b1 (sz (j - 8))
                  | 2 -> get_bit b2 (sz (j - 16))
                  | 3 -> get_bit b3 (sz (j - 24))
                  | 4 -> get_bit b4 (sz (j - 32))
                  | 5 -> get_bit b5 (sz (j - 40))
                  | 6 -> get_bit b6 (sz (j - 48))
                  | 7 -> get_bit b7 (sz (j - 56)))
              else 0))

val deserialize_4_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 8)
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          forall (i: nat{i < 256}).
            result i =
            (if i % 16 >= 4
              then 0
              else
                let j = (i / 16) * 4 + i % 16 in
                bit_vec_of_int_t_array (bytes <: t_Array _ (sz 8)) 8 j))

val serialize_5_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (mk_usize 10)) Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm256_si256_from_two_si128 as mm256_si256_from_two_si128}

val deserialize_5_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires Seq.length bytes == 10)
      (fun _ -> Prims.l_True)

val serialize_10___serialize_10_vec (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure
      (Libcrux_intrinsics.Avx2_extract.t_Vec128 & Libcrux_intrinsics.Avx2_extract.t_Vec128)
      (requires forall (i: nat{i < 256}). i % 16 < 10 || vector i = 0)
      (ensures
        fun temp_0_ ->
          let lower_8_, upper_8_:(Libcrux_intrinsics.Avx2_extract.t_Vec128 &
            Libcrux_intrinsics.Avx2_extract.t_Vec128) =
            temp_0_
          in
          forall (i: nat{i < 160}).
            vector ((i / 10) * 16 + i % 10) == (if i < 80 then lower_8_ i else upper_8_ (i - 80)))

val serialize_10_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (mk_usize 20))
      (requires forall (i: nat{i < 256}). i % 16 < 10 || vector i = 0)
      (ensures
        fun r ->
          let r:t_Array u8 (mk_usize 20) = r in
          forall (i: nat{i < 160}). bit_vec_of_int_t_array r 8 i == vector ((i / 10) * 16 + i % 10))

val deserialize_10___deserialize_10_vec
      (lower_coefficients0 upper_coefficients0: Libcrux_intrinsics.Avx2_extract.t_Vec128)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      Prims.l_True
      (ensures
        fun coefficients ->
          let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 = coefficients in
          forall (i: nat{i < 256}).
            coefficients i =
            (if i % 16 >= 10
              then 0
              else
                let j = (i / 16) * 10 + i % 16 in
                if i < 128 then lower_coefficients0 j else upper_coefficients0 (j - 32)))

val deserialize_10_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires Seq.length bytes == 20)
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          forall (i: nat{i < 256}).
            result i =
            (if i % 16 >= 10
              then 0
              else
                let j = (i / 16) * 10 + i % 16 in
                bit_vec_of_int_t_array (bytes <: t_Array _ (sz 20)) 8 j))

val serialize_11_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (mk_usize 22)) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_11_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val serialize_12___serialize_12_vec (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure
      (Libcrux_intrinsics.Avx2_extract.t_Vec128 & Libcrux_intrinsics.Avx2_extract.t_Vec128)
      (requires forall (i: nat{i < 256}). i % 16 < 12 || vector i = 0)
      (ensures
        fun temp_0_ ->
          let lower_8_, upper_8_:(Libcrux_intrinsics.Avx2_extract.t_Vec128 &
            Libcrux_intrinsics.Avx2_extract.t_Vec128) =
            temp_0_
          in
          forall (i: nat{i < 192}).
            vector ((i / 12) * 16 + i % 12) == (if i < 96 then lower_8_ i else upper_8_ (i - 96)))

val serialize_12_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 (mk_usize 24))
      (requires forall (i: nat{i < 256}). i % 16 < 12 || vector i = 0)
      (ensures
        fun r ->
          let r:t_Array u8 (mk_usize 24) = r in
          forall (i: nat{i < 192}). bit_vec_of_int_t_array r 8 i == vector ((i / 12) * 16 + i % 12))

val deserialize_12___deserialize_12_vec
      (lower_coefficients0 upper_coefficients0: Libcrux_intrinsics.Avx2_extract.t_Vec128)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      Prims.l_True
      (ensures
        fun coefficients ->
          let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 = coefficients in
          forall (i: nat{i < 256}).
            coefficients i =
            (if i % 16 >= 12
              then 0
              else
                let j = (i / 16) * 12 + i % 16 in
                if i < 128 then lower_coefficients0 j else upper_coefficients0 (j - 64)))

val deserialize_12_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires Seq.length bytes == 24)
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          forall (i: nat{i < 256}).
            result i =
            (if i % 16 >= 12
              then 0
              else
                let j = (i / 16) * 12 + i % 16 in
                bit_vec_of_int_t_array (bytes <: t_Array _ (sz 24)) 8 j))
