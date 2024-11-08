module Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let serialize (v_OUTPUT_SIZE: usize) (simd_unit: u8) =
  let serialized:t_Array u8 (sz 19) = Rust_primitives.Hax.repeat 0uy (sz 19) in
  match cast (v_OUTPUT_SIZE <: usize) <: u8 with
  | 4uy ->
    let adjacent_2_combined:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit
        (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 28l 0l 28l 0l 28l 0l 28l <: u8)
    in
    let adjacent_2_combined:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 28l adjacent_2_combined
    in
    let adjacent_4_combined:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_2_combined
        (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 0l 0l 6l 2l 4l 0l <: u8)
    in
    let adjacent_4_combined:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_4_combined
    in
    let adjacent_4_combined:u8 =
      Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 adjacent_4_combined
        (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 240uy 240uy 240uy 240uy 240uy 240uy 240uy 240uy
            240uy 240uy 240uy 240uy 12uy 4uy 8uy 0uy
          <:
          u8)
    in
    let serialized:t_Array u8 (sz 19) =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
        ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
          <:
          Core.Ops.Range.t_Range usize)
        (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = sz 16
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            adjacent_4_combined
          <:
          t_Slice u8)
    in
    Core.Result.impl__unwrap #(t_Array u8 v_OUTPUT_SIZE)
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice u8)
          #(t_Array u8 v_OUTPUT_SIZE)
          #FStar.Tactics.Typeclasses.solve
          (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        Core.Result.t_Result (t_Array u8 v_OUTPUT_SIZE) Core.Array.t_TryFromSliceError)
  | 6uy ->
    let adjacent_2_combined:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit
        (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 26l 0l 26l 0l 26l 0l 26l <: u8)
    in
    let adjacent_2_combined:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 26l adjacent_2_combined
    in
    let adjacent_3_combined:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_2_combined
        (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
            (-1y) (-1y) (-1y) (-1y) (-1y) 9y 8y 1y 0y (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
            (-1y) (-1y) (-1y) (-1y) (-1y) 9y 8y 1y 0y
          <:
          u8)
    in
    let adjacent_3_combined:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 adjacent_3_combined
        (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 1s 1s 1s 1s 1s 1s 1s (1s <<! 4l <: i16) 1s
            1s 1s 1s 1s 1s 1s (1s <<! 4l <: i16)
          <:
          u8)
    in
    let adjacent_3_combined:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 adjacent_3_combined
        (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 0l 4l 0l 0l 0l 4l <: u8)
    in
    let lower_3_:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_3_combined in
    let serialized:t_Array u8 (sz 19) =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
        ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
          <:
          Core.Ops.Range.t_Range usize)
        (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = sz 16
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            lower_3_
          <:
          t_Slice u8)
    in
    let upper_3_:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l adjacent_3_combined
    in
    let serialized:t_Array u8 (sz 19) =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
        ({ Core.Ops.Range.f_start = sz 3; Core.Ops.Range.f_end = sz 19 }
          <:
          Core.Ops.Range.t_Range usize)
        (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                  Core.Ops.Range.f_start = sz 3;
                  Core.Ops.Range.f_end = sz 19
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            upper_3_
          <:
          t_Slice u8)
    in
    Core.Result.impl__unwrap #(t_Array u8 v_OUTPUT_SIZE)
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice u8)
          #(t_Array u8 v_OUTPUT_SIZE)
          #FStar.Tactics.Typeclasses.solve
          (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 6 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        Core.Result.t_Result (t_Array u8 v_OUTPUT_SIZE) Core.Array.t_TryFromSliceError)
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
