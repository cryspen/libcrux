module Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_eta
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let shift_interval (v_ETA: usize) (coefficients: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  match cast (v_ETA <: usize) <: u8 with
  | 2 ->
    let quotient:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
      Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 coefficients
        (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (Rust_primitives.mk_i32 26)
          <:
          Libcrux_intrinsics.Avx2_extract.t_Vec256)
    in
    let quotient:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
      Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 (Rust_primitives.mk_i32 7) quotient
    in
    let quotient:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
      Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 quotient
        (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (Rust_primitives.mk_i32 5)
          <:
          Libcrux_intrinsics.Avx2_extract.t_Vec256)
    in
    let coefficients_mod_5_:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
      Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 coefficients quotient
    in
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          (cast (v_ETA <: usize) <: i32)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      coefficients_mod_5_
  | 4 ->
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          (cast (v_ETA <: usize) <: i32)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      coefficients
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let sample (v_ETA: usize) (input: t_Slice u8) (output: t_Slice i32) =
  let potential_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.deserialize_to_unsigned (Rust_primitives.mk_usize 4)
      input
  in
  let (interval_boundary: i32):i32 =
    match cast (v_ETA <: usize) <: u8 with
    | 2 -> Rust_primitives.mk_i32 15
    | 4 -> Rust_primitives.mk_i32 9
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let compare_with_interval_boundary:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          interval_boundary
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      potential_coefficients
  in
  let good:i32 =
    Libcrux_intrinsics.Avx2_extract.mm256_movemask_ps (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_ps
          compare_with_interval_boundary
        <:
        u8)
  in
  let good_lower_half:i32 = good &. Rust_primitives.mk_i32 15 in
  let good_upper_half:i32 = good >>! Rust_primitives.mk_i32 4 in
  let shifted:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    shift_interval v_ETA potential_coefficients
  in
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
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 shifted
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
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (Rust_primitives.mk_i32 1) shifted
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
