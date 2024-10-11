module Libcrux_ml_dsa.Simd.Avx2.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let change_interval (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let interval_end:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (Rust_primitives.mk_i32 1 <<!
        (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! Rust_primitives.mk_usize 1 <: usize)
        <:
        i32)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 interval_end simd_unit

let deserialize (serialized: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.impl__len #u8 serialized, Rust_primitives.mk_usize 13 <: (usize & usize)
        with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let serialized_extended:t_Array u8 (Rust_primitives.mk_usize 16) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 16)
  in
  let serialized_extended:t_Array u8 (Rust_primitives.mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized_extended
      ({
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
          Core.Ops.Range.f_end = Rust_primitives.mk_usize 13
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized_extended.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
                Core.Ops.Range.f_end = Rust_primitives.mk_usize 13
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          serialized
        <:
        t_Slice u8)
  in
  let serialized:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (serialized_extended <: t_Slice u8)
  in
  let serialized:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_m128i serialized serialized
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 serialized
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 12) (Rust_primitives.mk_i8 11)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 11) (Rust_primitives.mk_i8 10)
          (Rust_primitives.mk_i8 9) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 9) (Rust_primitives.mk_i8 8) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 8) (Rust_primitives.mk_i8 7) (Rust_primitives.mk_i8 6)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 6) (Rust_primitives.mk_i8 5)
          (Rust_primitives.mk_i8 4) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 4) (Rust_primitives.mk_i8 3) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 3) (Rust_primitives.mk_i8 2) (Rust_primitives.mk_i8 1)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 1)
          (Rust_primitives.mk_i8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 3)
          (Rust_primitives.mk_i32 6)
          (Rust_primitives.mk_i32 1)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 7)
          (Rust_primitives.mk_i32 2)
          (Rust_primitives.mk_i32 5)
          (Rust_primitives.mk_i32 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize__COEFFICIENT_MASK
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  change_interval coefficients

let serialize (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (Rust_primitives.mk_usize 16) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 16)
  in
  let simd_unit:Libcrux_intrinsics.Avx2_extract.t_Vec256 = change_interval simd_unit in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 19)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 19)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 19)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 19)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (Rust_primitives.mk_i32 19) adjacent_2_combined
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 6)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 2)
          (Rust_primitives.mk_i32 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 6)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 6)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 6)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 6)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (Rust_primitives.mk_i32 6) adjacent_4_combined
  in
  let second_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_bsrli_epi128 (Rust_primitives.mk_i32 8)
      adjacent_4_combined
  in
  let least_12_bits_shifted_up:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi64 (Rust_primitives.mk_i32 52) second_4_combined
  in
  let bits_sequential:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi64 adjacent_4_combined least_12_bits_shifted_up
  in
  let bits_sequential:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi64 bits_sequential
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi64x (Rust_primitives.mk_i64 0)
          (Rust_primitives.mk_i64 0)
          (Rust_primitives.mk_i64 12)
          (Rust_primitives.mk_i64 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let bits_sequential:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 bits_sequential
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 16) =
    Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 serialized bits_sequential
  in
  Core.Result.impl__unwrap #(t_Array u8 (Rust_primitives.mk_usize 13))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (Rust_primitives.mk_usize 13))
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ {
              Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
              Core.Ops.Range.f_end = Rust_primitives.mk_usize 13
            }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (Rust_primitives.mk_usize 13)) Core.Array.t_TryFromSliceError
    )
