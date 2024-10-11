module Libcrux_ml_dsa.Simd.Avx2.Encoding.T1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let serialize (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (Rust_primitives.mk_usize 24) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 24)
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 22)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 22)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 22)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 22)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (Rust_primitives.mk_i32 22) adjacent_2_combined
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 6)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 2)
          (Rust_primitives.mk_i32 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 12)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 12)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 12)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 12)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (Rust_primitives.mk_i32 12) adjacent_4_combined
  in
  let lower_4_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_4_combined
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
          Core.Ops.Range.f_end = Rust_primitives.mk_usize 16
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
                Core.Ops.Range.f_end = Rust_primitives.mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_4_
        <:
        t_Slice u8)
  in
  let upper_4_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (Rust_primitives.mk_i32 1)
      adjacent_4_combined
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 5;
          Core.Ops.Range.f_end = Rust_primitives.mk_usize 21
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 5;
                Core.Ops.Range.f_end = Rust_primitives.mk_usize 21
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_4_
        <:
        t_Slice u8)
  in
  Core.Result.impl__unwrap #(t_Array u8 (Rust_primitives.mk_usize 10))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (Rust_primitives.mk_usize 10))
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ {
              Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
              Core.Ops.Range.f_end = Rust_primitives.mk_usize 10
            }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (Rust_primitives.mk_usize 10)) Core.Array.t_TryFromSliceError
    )

let deserialize (bytes: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 bytes, Rust_primitives.mk_usize 10 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let bytes_extended:t_Array u8 (Rust_primitives.mk_usize 16) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 16)
  in
  let bytes_extended:t_Array u8 (Rust_primitives.mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes_extended
      ({
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
          Core.Ops.Range.f_end = Rust_primitives.mk_usize 10
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (bytes_extended.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
                Core.Ops.Range.f_end = Rust_primitives.mk_usize 10
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          bytes
        <:
        t_Slice u8)
  in
  let bytes_loaded:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (bytes_extended <: t_Slice u8)
  in
  let bytes_loaded:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_m128i bytes_loaded bytes_loaded
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 bytes_loaded
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 9) (Rust_primitives.mk_i8 8)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 8)
          (Rust_primitives.mk_i8 7) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 7) (Rust_primitives.mk_i8 6) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 6) (Rust_primitives.mk_i8 5)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 4)
          (Rust_primitives.mk_i8 3) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 3) (Rust_primitives.mk_i8 2) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 2) (Rust_primitives.mk_i8 1)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 1)
          (Rust_primitives.mk_i8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 6)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 2)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 6)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 2)
          (Rust_primitives.mk_i32 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize__COEFFICIENT_MASK
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)
