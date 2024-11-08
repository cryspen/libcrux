module Libcrux_ml_dsa.Simd.Avx2.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let change_interval (simd_unit: u8) =
  let interval_end:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (1l <<!
        (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! sz 1 <: usize)
        <:
        i32)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 interval_end simd_unit

let deserialize (serialized: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 serialized, sz 13 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let serialized_extended:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let serialized_extended:t_Array u8 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized_extended
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 13 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized_extended.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 13 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          serialized
        <:
        t_Slice u8)
  in
  let serialized:u8 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (serialized_extended <: t_Slice u8)
  in
  let serialized:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set_m128i serialized serialized in
  let coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 serialized
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) (-1y) 12y 11y (-1y) 11y 10y 9y (-1y)
          (-1y) 9y 8y (-1y) 8y 7y 6y (-1y) 6y 5y 4y (-1y) (-1y) 4y 3y (-1y) 3y 2y 1y (-1y) (-1y) 1y
          0y
        <:
        u8)
  in
  let coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 3l 6l 1l 4l 7l 2l 5l 0l <: u8)
  in
  let coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize__COEFFICIENT_MASK <: u8)
  in
  change_interval coefficients

let serialize (simd_unit: u8) =
  let serialized:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let simd_unit:u8 = change_interval simd_unit in
  let adjacent_2_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 19l 0l 19l 0l 19l 0l 19l <: u8)
  in
  let adjacent_2_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 19l adjacent_2_combined
  in
  let adjacent_4_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 0l 0l 6l 4l 2l 0l <: u8)
  in
  let adjacent_4_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 6l 0l 6l 0l 6l 0l 6l <: u8)
  in
  let adjacent_4_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 6l adjacent_4_combined
  in
  let second_4_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_bsrli_epi128 8l adjacent_4_combined
  in
  let least_12_bits_shifted_up:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi64 52l second_4_combined
  in
  let bits_sequential:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi64 adjacent_4_combined least_12_bits_shifted_up
  in
  let bits_sequential:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi64 bits_sequential
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi64x 0L 0L 12L 0L <: u8)
  in
  let bits_sequential:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 bits_sequential in
  let serialized:t_Array u8 (sz 16) =
    Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 serialized bits_sequential
  in
  Core.Result.impl__unwrap #(t_Array u8 (sz 13))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (sz 13))
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 13 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (sz 13)) Core.Array.t_TryFromSliceError)
