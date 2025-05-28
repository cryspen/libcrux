module Libcrux_ml_dsa.Simd.Avx2.Encoding.T1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

open Spec.Intrinsics

#push-options "--fuel 0 --ifuel 0 --z3rlimit 5000 --split_queries always"
let serialize
  (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (out: t_Slice u8 { ((Core.Slice.impl__len #u8 out <: usize) =. mk_usize 10 <: bool)})
   : Pure (t_Slice u8)
     (requires True)
     (ensures fun result -> Seq.length result = 10 /\
         (forall (i:nat).
           i < 80 ==> (
           let q10 = i / 10 in
           let r10 = i % 10 in
           let q8 = i / 8 in
           let r8 = i % 8 in
           (simd_unit.(mk_int (32*q10 + r10)) == (u8_to_bv (Seq.index result q8))(mk_int r8))
           )))
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 out <: usize) =. mk_usize 10 <: bool)
      in
      ()
  in

  let serialized_init : t_Array u8 (mk_usize 24) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 24) in

  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 22)
          (mk_i32 0)
          (mk_i32 22)
          (mk_i32 0)
          (mk_i32 22)
          (mk_i32 0)
          (mk_i32 22)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 22) adjacent_2_combined
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 4)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 2)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 12)
          (mk_i32 0)
          (mk_i32 12)
          (mk_i32 0)
          (mk_i32 12)
          (mk_i32 0)
          (mk_i32 12)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 12) adjacent_4_combined
  in
  let lower_4_:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 adjacent_4_combined
  in

  // Lower 40 bits are correct
  // assert (forall (i q r: nat).
  //   i < 40 ==> (
  //   q = i / 10 ==>
  //   r = i % 10 ==>
  //   simd_unit.(mk_int (32 * q + r)) == lower_4_.(mk_int(10*q + r)) ));

  let pre_serialized_lower = (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized_init.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_4_
        <:
        t_Slice u8) in

  let serialized_lower:t_Array u8 (mk_usize 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized_init
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      pre_serialized_lower
  in

  // // Monomorphized update is the identity
  // assert (forall i. (Seq.index pre_serialized_lower i) == (Seq.index serialized_lower i));

  // // First part [0;39] of serialized is correct
  // assert (forall (i q10 r10 q8 r8: nat).
  //   i < 40 ==> (
  //   q10 = i / 10 ==>
  //   r10 = i % 10 ==>
  //   q8 = i / 8 ==>
  //   r8 = i % 8 ==>
  //   simd_unit.(mk_int (32 * q10 + r10)) == (u8_to_bv (Seq.index serialized_lower q8))(mk_int r8)
  //   ));

  let upper_4_:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_extracti128_si256 (mk_i32 1) adjacent_4_combined
  in

  //upper 40 are correct
  // assert (forall (q r :nat). q < 4 ==> r < 10 ==> (
  // (simd_unit.(mk_int (128 + 32*q + r)) == upper_4_.(mk_int (10*q + r)))))
  //;

  let pre_serialized_upper = (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized_lower.[ {
                Core.Ops.Range.f_start = mk_usize 5;
                Core.Ops.Range.f_end = mk_usize 21
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_4_
        <:
        t_Slice u8) in

  // // pre_serialized_upper is correctly populated
  // assert (forall i.
  //   i >= 40 ==>
  //   i < 80 ==> (
  //   let q10 = i / 10 in
  //   let r10 = i % 10 in
  //   let q8 = i / 8 in
  //   let r8 = i % 8 in
  //   (u8_to_bv (Seq.index pre_serialized_upper (q8 - 5)))(mk_int r8) == upper_4_.(mk_int (10*(q10-4) + r10))
  // ));

  let serialized_upper:t_Array u8 (mk_usize 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized_lower
      ({ Core.Ops.Range.f_start = mk_usize 5; Core.Ops.Range.f_end = mk_usize 21 }
        <:
        Core.Ops.Range.t_Range usize)
      pre_serialized_upper
  in

  // // Monomorphized update is the identity
  // assert (forall j. j < 5 ==>
  // (Seq.index serialized_upper (j + 5)) == (Seq.index pre_serialized_upper j));


  // // serialized_upper is correctly populated
  // assert (forall i.
  //   i >= 40 ==>
  //   i < 80 ==> (
  //   let q10 = i / 10 in
  //   let r10 = i % 10 in
  //   let q8 = i / 8 in
  //   let r8 = i % 8 in
  //   (u8_to_bv (Seq.index serialized_upper q8))(mk_int r8) == upper_4_.(mk_int (10*(q10-4) + r10))
  // ));

  //Second part [40;79] of serialized is correct
  assert (forall i.
    i >= 40 ==>
    i < 80 ==> (
    let q10 = i / 10 in
    let r10 = i % 10 in
    let q8 = i / 8 in
    let r8 = i % 8 in
    simd_unit.(mk_int (32*q10 + r10)) == upper_4_.(mk_int (10*(q10-4) + r10))
   /\  upper_4_.(mk_int (10*(q10-4) + r10)) == (u8_to_bv (Seq.index pre_serialized_upper (q8 - 5)))(mk_int r8)
   /\  (u8_to_bv (Seq.index pre_serialized_upper (q8 - 5)))(mk_int r8) == (u8_to_bv (Seq.index serialized_upper q8))(mk_int r8)
  ));

  let out:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      out
      (serialized_upper.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 10 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let deserialize__v_COEFFICIENT_MASK: i32 = (mk_i32 1 <<! mk_i32 10 <: i32) -! mk_i32 1

let deserialize
(bytes: t_Slice u8)
(out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 bytes, mk_usize 10 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let bytes_extended:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16)
  in
  let bytes_extended:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes_extended
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 10 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (bytes_extended.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 10
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          bytes
        <:
        t_Slice u8)
  in
  let bytes_loaded:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm_loadu_si128 (bytes_extended <: t_Slice u8)
  in
  let bytes_loaded:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set_m128i bytes_loaded bytes_loaded
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 bytes_loaded
      (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 9) (mk_i8 8)
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 8) (mk_i8 7) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 7)
          (mk_i8 6) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 6) (mk_i8 5) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 4) (mk_i8 3) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 3) (mk_i8 2) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 2) (mk_i8 1) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 1) (mk_i8 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 6)
          (mk_i32 4)
          (mk_i32 2)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 4)
          (mk_i32 2)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let out:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize__v_COEFFICIENT_MASK
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  out
