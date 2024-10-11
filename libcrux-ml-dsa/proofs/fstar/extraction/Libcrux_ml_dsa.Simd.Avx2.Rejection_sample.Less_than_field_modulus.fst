module Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_field_modulus
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let bytestream_to_potential_coefficients (serialized: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.impl__len #u8 serialized, Rust_primitives.mk_usize 24 <: (usize & usize)
        with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let serialized_extended:t_Array u8 (Rust_primitives.mk_usize 32) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 32)
  in
  let serialized_extended:t_Array u8 (Rust_primitives.mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to serialized_extended
      ({ Core.Ops.Range.f_end = Rust_primitives.mk_usize 24 } <: Core.Ops.Range.t_RangeTo usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized_extended.[ { Core.Ops.Range.f_end = Rust_primitives.mk_usize 24 }
              <:
              Core.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
          serialized
        <:
        t_Slice u8)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_u8 (serialized_extended <: t_Slice u8)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 5)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 3)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 2)
          (Rust_primitives.mk_i32 1)
          (Rust_primitives.mk_i32 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 11) (Rust_primitives.mk_i8 10) (Rust_primitives.mk_i8 9)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 8) (Rust_primitives.mk_i8 7)
          (Rust_primitives.mk_i8 6) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 5)
          (Rust_primitives.mk_i8 4) (Rust_primitives.mk_i8 3) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 2) (Rust_primitives.mk_i8 1) (Rust_primitives.mk_i8 0)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 11) (Rust_primitives.mk_i8 10)
          (Rust_primitives.mk_i8 9) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 8)
          (Rust_primitives.mk_i8 7) (Rust_primitives.mk_i8 6) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 5) (Rust_primitives.mk_i8 4) (Rust_primitives.mk_i8 3)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 2) (Rust_primitives.mk_i8 1)
          (Rust_primitives.mk_i8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 bytestream_to_potential_coefficients__COEFFICIENT_MASK

      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

let sample (input: t_Slice u8) (output: t_Slice i32) =
  let field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let potential_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    bytestream_to_potential_coefficients input
  in
  let compare_with_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 field_modulus potential_coefficients
  in
  let good:i32 =
    Libcrux_intrinsics.Avx2_extract.mm256_movemask_ps (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_ps
          compare_with_field_modulus
        <:
        u8)
  in
  let good_lower_half:i32 = good &. Rust_primitives.mk_i32 15 in
  let good_upper_half:i32 = good >>! Rust_primitives.mk_i32 4 in
  let lower_shuffles:t_Array u8 (Rust_primitives.mk_usize 16) =
    Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Shuffle_table.v_SHUFFLE_TABLE.[ cast (good_lower_half
          <:
          i32)
      <:
      usize ]
  in
  let lower_shuffles:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (lower_shuffles <: t_Slice u8)
  in
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 potential_coefficients
  in
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 lower_coefficients lower_shuffles
  in
  let output:t_Slice i32 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range output
      ({
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
          Core.Ops.Range.f_end = Rust_primitives.mk_usize 4
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_si128_i32 (output.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
                Core.Ops.Range.f_end = Rust_primitives.mk_usize 4
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
  let upper_shuffles:t_Array u8 (Rust_primitives.mk_usize 16) =
    Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Shuffle_table.v_SHUFFLE_TABLE.[ cast (good_upper_half
          <:
          i32)
      <:
      usize ]
  in
  let upper_shuffles:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (upper_shuffles <: t_Slice u8)
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (Rust_primitives.mk_i32 1)
      potential_coefficients
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 upper_coefficients upper_shuffles
  in
  let output:t_Slice i32 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range output
      ({
          Core.Ops.Range.f_start = sampled_count;
          Core.Ops.Range.f_end = sampled_count +! Rust_primitives.mk_usize 4 <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_si128_i32 (output.[ {
                Core.Ops.Range.f_start = sampled_count;
                Core.Ops.Range.f_end = sampled_count +! Rust_primitives.mk_usize 4 <: usize
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
