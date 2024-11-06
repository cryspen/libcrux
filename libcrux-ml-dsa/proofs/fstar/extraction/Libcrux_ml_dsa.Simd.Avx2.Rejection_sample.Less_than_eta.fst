module Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_eta
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let shift_interval (v_ETA: usize) (coefficients: u8) =
  match cast (v_ETA <: usize) <: u8 with
  | 2uy ->
    let quotient:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 coefficients
        (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 26l <: u8)
    in
    let quotient:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 7l quotient in
    let quotient:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 quotient
        (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 5l <: u8)
    in
    let coefficients_mod_5_:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 coefficients quotient
    in
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          (cast (v_ETA <: usize) <: i32)
        <:
        u8)
      coefficients_mod_5_
  | 4uy ->
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          (cast (v_ETA <: usize) <: i32)
        <:
        u8)
      coefficients
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let sample (v_ETA: usize) (input: t_Slice u8) (output: t_Slice i32) =
  let potential_coefficients:u8 =
    Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.deserialize_to_unsigned (sz 4) input
  in
  let (interval_boundary: i32):i32 =
    match cast (v_ETA <: usize) <: u8 with
    | 2uy -> 15l
    | 4uy -> 9l
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let compare_with_interval_boundary:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          interval_boundary
        <:
        u8)
      potential_coefficients
  in
  let good:i32 =
    Libcrux_intrinsics.Avx2_extract.mm256_movemask_ps (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_ps
          compare_with_interval_boundary
        <:
        u8)
  in
  let good_lower_half:i32 = good &. 15l in
  let good_upper_half:i32 = good >>! 4l in
  let shifted:u8 = shift_interval v_ETA potential_coefficients in
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
  let lower_coefficients:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 shifted in
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
  let upper_coefficients:u8 = Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l shifted in
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
