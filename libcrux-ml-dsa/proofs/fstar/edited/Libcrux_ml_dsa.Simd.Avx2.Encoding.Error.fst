module Libcrux_ml_dsa.Simd.Avx2.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

open Spec.Intrinsics

#push-options "--fuel 0 --ifuel 0 --z3rlimit 5000 --z3smtopt '(set-option :smt.arith.nl false)'"

let serialize_when_eta_is_2_aux
      (simd_unit_shifted: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
      (requires
        forall (i: nat{i < 256}).
          i % 32 >= 3 ==> simd_unit_shifted.(mk_int i) == Core_models.Abstractions.Bit.Bit_Zero)
      (ensures
        fun result ->
          let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) = result in
          forall (i: nat{i < 24}).
            result.(mk_int i) == simd_unit_shifted.(mk_int ((i / 3) * 32 + i % 3))) =
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit_shifted
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 29)
          (mk_i32 0)
          (mk_i32 29)
          (mk_i32 0)
          (mk_i32 29)
          (mk_i32 0)
          (mk_i32 29)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 29) adjacent_2_combined
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 8) (mk_i8 (-1)) (mk_i8 0) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 8) (mk_i8 (-1)) (mk_i8 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_madd_epi16 adjacent_4_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi16 (mk_i16 0) (mk_i16 0) (mk_i16 0) (mk_i16 0)
          (mk_i16 0) (mk_i16 0) (mk_i16 1 <<! mk_i32 6 <: i16) (mk_i16 1) (mk_i16 0) (mk_i16 0)
          (mk_i16 0) (mk_i16 0) (mk_i16 0) (mk_i16 0) (mk_i16 1 <<! mk_i32 6 <: i16) (mk_i16 1)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_6_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_permutevar8x32_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_6_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 adjacent_6_combined
  in
  let adjacent_6_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm_sllv_epi32 adjacent_6_combined
      (Libcrux_intrinsics.Avx2.mm_set_epi32 (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 20)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
  in
  Libcrux_intrinsics.Avx2.mm_srli_epi64 (mk_i32 20) adjacent_6_combined

#pop-options

let serialize_when_eta_is_2___v_ETA: i32 = mk_i32 2

let serialize_when_eta_is_2_
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        forall i.
          let x = (2 - v (to_i32x8 simd_unit i)) in
          x >= 0 && x <= 7)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          Seq.length out_future == 3 /\
          (forall (i: nat{i < 24}).
              u8_to_bv (Seq.index out_future (i / 8)) (mk_int (i % 8)) ==
              i32_to_bv (mk_int 2 -! to_i32x8 simd_unit (mk_int (i / 3))) (mk_int (i % 3)))) =
  let serialized:t_Array u8 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16) in
  let simd_unit_shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 serialize_when_eta_is_2___v_ETA

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      simd_unit
  in
  let _:Prims.unit = i32_lt_pow2_n_to_bit_zero_lemma 3 simd_unit_shifted in
  let adjacent_6_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    serialize_when_eta_is_2_aux simd_unit_shifted
  in
  let _:Prims.unit =
    assert (forall (i: nat{i < 24}).
          to_i32x8 simd_unit_shifted (mk_int (i / 3)) ==
          (mk_int 2)
          `sub_mod`
          (to_i32x8 simd_unit (mk_int (i / 3))))
  in
  let _:Prims.unit =
    assert (forall i.
          (mk_int 2) `sub_mod` (to_i32x8 simd_unit i) == mk_int 2 -! to_i32x8 simd_unit i)
  in
  let serialized:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          adjacent_6_combined
        <:
        t_Slice u8)
  in
  let out:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      out
      (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 3 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let serialize_when_eta_is_4_aux
      (simd_unit_shifted: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
      (requires
        forall (i: nat{i < 256}).
          i % 32 >= 4 ==> simd_unit_shifted.(mk_int i) == Core_models.Abstractions.Bit.Bit_Zero)
      (ensures
        fun result ->
          let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) = result in
          forall (i: nat{i < 32}).
            result.(mk_int i) == simd_unit_shifted.(mk_int ((i / 4) * 32 + i % 4))) =
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit_shifted
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 28)
          (mk_i32 0)
          (mk_i32 28)
          (mk_i32 0)
          (mk_i32 28)
          (mk_i32 0)
          (mk_i32 28)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 28) adjacent_2_combined
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 2)
          (mk_i32 4)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 adjacent_4_combined
  in
  Libcrux_intrinsics.Avx2.mm_shuffle_epi8 adjacent_4_combined
    (Libcrux_intrinsics.Avx2.mm_set_epi8 (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240)
        (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240)
        (mk_u8 12) (mk_u8 4) (mk_u8 8) (mk_u8 0)
      <:
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))

let serialize_when_eta_is_4___v_ETA: i32 = mk_i32 4

#push-options "--split_queries always"

let serialize_when_eta_is_4_
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        forall i.
          let x = (4 - v (to_i32x8 simd_unit i)) in
          x >= 0 && x <= 15)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          Seq.length out_future == 4 /\
          (forall (i: nat{i < 32}).
              u8_to_bv (Seq.index out_future (i / 8)) (mk_int (i % 8)) ==
              i32_to_bv (mk_int 4 -! to_i32x8 simd_unit (mk_int (i / 4))) (mk_int (i % 4)))) =
  let serialized:t_Array u8 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16) in
  let simd_unit_shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 serialize_when_eta_is_4___v_ETA

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      simd_unit
  in
  let _:Prims.unit = i32_lt_pow2_n_to_bit_zero_lemma 4 simd_unit_shifted in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    serialize_when_eta_is_4_aux simd_unit_shifted
  in
  let _:Prims.unit =
    assert (forall (i: nat{i < 32}).
          to_i32x8 simd_unit_shifted (mk_int (i / 4)) ==
          (mk_int 4)
          `sub_mod`
          (to_i32x8 simd_unit (mk_int (i / 4))))
  in
  let _:Prims.unit =
    assert (forall i.
          (mk_int 4) `sub_mod` (to_i32x8 simd_unit i) == mk_int 4 -! to_i32x8 simd_unit i)
  in
  let serialized:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          adjacent_4_combined
        <:
        t_Slice u8)
  in
  let out:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      out
      (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 4 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

#pop-options

let serialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        forall i.
          let x =
            (v (cast (Libcrux_ml_dsa.Constants.t_Eta_cast_to_repr eta <: isize) <: u8) -
              v (to_i32x8 simd_unit i))
          in
          x >= 0 &&
          x <=
          (pow2 (v (cast (Libcrux_ml_dsa.Constants.t_Eta_cast_to_repr eta <: isize) <: u8)) - 1))
      (ensures
        fun serialized_future ->
          let serialized_future:t_Slice u8 = serialized_future in
          let bytes:i32 =
            match eta <: Libcrux_ml_dsa.Constants.t_Eta with
            | Libcrux_ml_dsa.Constants.Eta_Two  -> mk_i32 3
            | Libcrux_ml_dsa.Constants.Eta_Four  -> mk_i32 4
          in
          Seq.length serialized_future == v bytes /\
          (forall (i: nat{i < v bytes * 8}).
              u8_to_bv (Seq.index serialized_future (i / 8)) (mk_int (i % 8)) ==
              i32_to_bv ((cast (Libcrux_ml_dsa.Constants.t_Eta_cast_to_repr eta <: isize) <: i32) -!
                  to_i32x8 simd_unit (mk_int (i / v bytes)))
                (mk_int (i % v bytes)))) =
  let serialized:t_Slice u8 =
    match eta <: Libcrux_ml_dsa.Constants.t_Eta with
    | Libcrux_ml_dsa.Constants.Eta_Two  -> serialize_when_eta_is_2_ simd_unit serialized
    | Libcrux_ml_dsa.Constants.Eta_Four  -> serialize_when_eta_is_4_ simd_unit serialized
  in
  serialized

let deserialize_to_unsigned_when_eta_is_2___v_COEFFICIENT_MASK: i32 =
  (mk_i32 1 <<! mk_i32 3 <: i32) -! mk_i32 1

let deserialize_to_unsigned_when_eta_is_2_ (bytes: t_Slice u8)
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 3)
      (ensures
        fun result ->
          let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = result in
          (forall (i: nat{i < 24}).
              u8_to_bv bytes.[ mk_usize (i / 8) ] (mk_int (i % 8)) ==
              result.(mk_int ((i / 3) * 32 + i % 3))) /\
          (forall (i: nat{i < 256}).
              i % 32 >= 3 ==> Core_models.Abstractions.Bit.Bit_Zero? result.(mk_int i))) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 3 <: bool)
      in
      ()
  in
  let bytes_in_simd_unit:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set_epi32 (cast (bytes.[ mk_usize 2 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 2 ] <: u8) <: i32)
      (((cast (bytes.[ mk_usize 2 ] <: u8) <: i32) <<! mk_i32 8 <: i32) |.
        (cast (bytes.[ mk_usize 1 ] <: u8) <: i32)
        <:
        i32)
      (cast (bytes.[ mk_usize 1 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 1 ] <: u8) <: i32)
      (((cast (bytes.[ mk_usize 1 ] <: u8) <: i32) <<! mk_i32 8 <: i32) |.
        (cast (bytes.[ mk_usize 0 ] <: u8) <: i32)
        <:
        i32)
      (cast (bytes.[ mk_usize 0 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 0 ] <: u8) <: i32)
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 bytes_in_simd_unit
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 5)
          (mk_i32 2)
          (mk_i32 7)
          (mk_i32 4)
          (mk_i32 1)
          (mk_i32 6)
          (mk_i32 3)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_to_unsigned_when_eta_is_2___v_COEFFICIENT_MASK

      <:
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))

let deserialize_to_unsigned_when_eta_is_4___v_COEFFICIENT_MASK: i32 =
  (mk_i32 1 <<! mk_i32 4 <: i32) -! mk_i32 1

let deserialize_to_unsigned_when_eta_is_4_ (bytes: t_Slice u8)
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 4)
      (ensures
        fun result ->
          let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = result in
          (forall (i: nat{i < 32}).
              u8_to_bv bytes.[ mk_usize (i / 8) ] (mk_int (i % 8)) ==
              result.(mk_int ((i / 4) * 32 + i % 4))) /\
          (forall (i: nat{i < 256}).
              i % 32 >= 4 ==> Core_models.Abstractions.Bit.Bit_Zero? result.(mk_int i))) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 4 <: bool)
      in
      ()
  in
  let bytes_in_simd_unit:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set_epi32 (cast (bytes.[ mk_usize 3 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 3 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 2 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 2 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 1 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 1 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 0 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 0 ] <: u8) <: i32)
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 bytes_in_simd_unit
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 4)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_to_unsigned_when_eta_is_4___v_COEFFICIENT_MASK

      <:
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))

let deserialize_to_unsigned (eta: Libcrux_ml_dsa.Constants.t_Eta) (serialized: t_Slice u8)
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        (match eta <: Libcrux_ml_dsa.Constants.t_Eta with
          | Libcrux_ml_dsa.Constants.Eta_Two  -> mk_usize 3
          | Libcrux_ml_dsa.Constants.Eta_Four  -> mk_usize 4))
      (ensures
        fun result ->
          let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = result in
          let bytes = Seq.length serialized in
          (forall (i: nat{i < bytes * 8}).
              u8_to_bv serialized.[ mk_usize (i / 8) ] (mk_int (i % 8)) ==
              result.(mk_int ((i / bytes) * 32 + i % bytes))) /\
          (forall (i: nat{i < 256}).
              i % 32 >= bytes ==> Core_models.Abstractions.Bit.Bit_Zero? result.(mk_int i))) =
  match eta <: Libcrux_ml_dsa.Constants.t_Eta with
  | Libcrux_ml_dsa.Constants.Eta_Two  -> deserialize_to_unsigned_when_eta_is_2_ serialized
  | Libcrux_ml_dsa.Constants.Eta_Four  -> deserialize_to_unsigned_when_eta_is_4_ serialized

let deserialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (serialized: t_Slice u8)
      (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        (match eta <: Libcrux_ml_dsa.Constants.t_Eta with
          | Libcrux_ml_dsa.Constants.Eta_Two  -> mk_usize 3
          | Libcrux_ml_dsa.Constants.Eta_Four  -> mk_usize 4))
      (fun _ -> Prims.l_True) =
  let unsigned:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    deserialize_to_unsigned eta serialized
  in
  let eta:i32 =
    match eta <: Libcrux_ml_dsa.Constants.t_Eta with
    | Libcrux_ml_dsa.Constants.Eta_Two  -> mk_i32 2
    | Libcrux_ml_dsa.Constants.Eta_Four  -> mk_i32 4
  in
  let out:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 eta
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      unsigned
  in
  out
