module Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_field_modulus
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let bytestream_to_potential_coefficients (serialized: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 serialized, sz 24 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let serialized_extended:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let serialized_extended:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to serialized_extended
      ({ Core.Ops.Range.f_end = sz 24 } <: Core.Ops.Range.t_RangeTo usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized_extended.[ { Core.Ops.Range.f_end = sz 24 } <: Core.Ops.Range.t_RangeTo usize
            ]
            <:
            t_Slice u8)
          serialized
        <:
        t_Slice u8)
  in
  let coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_u8 (serialized_extended <: t_Slice u8)
  in
  let coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 5l 4l 3l 0l 2l 1l 0l <: u8)
  in
  let coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) 11y 10y 9y (-1y) 8y 7y 6y (-1y) 5y 4y 3y
          (-1y) 2y 1y 0y (-1y) 11y 10y 9y (-1y) 8y 7y 6y (-1y) 5y 4y 3y (-1y) 2y 1y 0y
        <:
        u8)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 bytestream_to_potential_coefficients__COEFFICIENT_MASK

      <:
      u8)

let sample (input: t_Slice u8) (output: t_Slice i32) =
  let field_modulus:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let potential_coefficients:u8 = bytestream_to_potential_coefficients input in
  let compare_with_field_modulus:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 field_modulus potential_coefficients
  in
  let good:i32 =
    Libcrux_intrinsics.Avx2_extract.mm256_movemask_ps (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_ps
          compare_with_field_modulus
        <:
        u8)
  in
  let good_lower_half:i32 = good &. 15l in
  let good_upper_half:i32 = good >>! 4l in
  let lower_shuffles:t_Array u8 (sz 16) =
    Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Shuffle_table.v_SHUFFLE_TABLE.[ cast (good_lower_half
          <:
          i32)
      <:
      usize ]
  in
  let lower_shuffles:u8 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (lower_shuffles <: t_Slice u8)
  in
  let lower_coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 potential_coefficients
  in
  let lower_coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 lower_coefficients lower_shuffles
  in
  let output:t_Slice i32 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range output
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_si128_i32 (output.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = sz 4
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i32)
          lower_coefficients
        <:
        t_Slice i32)
  in
  let sampled_count:usize = cast (Core.Num.impl__i32__count_ones good_lower_half <: u32) <: usize in
  let upper_shuffles:t_Array u8 (sz 16) =
    Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Shuffle_table.v_SHUFFLE_TABLE.[ cast (good_upper_half
          <:
          i32)
      <:
      usize ]
  in
  let upper_shuffles:u8 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (upper_shuffles <: t_Slice u8)
  in
  let upper_coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l potential_coefficients
  in
  let upper_coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 upper_coefficients upper_shuffles
  in
  let output:t_Slice i32 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range output
      ({
          Core.Ops.Range.f_start = sampled_count;
          Core.Ops.Range.f_end = sampled_count +! sz 4 <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_si128_i32 (output.[ {
                Core.Ops.Range.f_start = sampled_count;
                Core.Ops.Range.f_end = sampled_count +! sz 4 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i32)
          upper_coefficients
        <:
        t_Slice i32)
  in
  let hax_temp_output:usize =
    sampled_count +! (cast (Core.Num.impl__i32__count_ones good_upper_half <: u32) <: usize)
  in
  output, hax_temp_output <: (t_Slice i32 & usize)
