module Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let serialize (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice u8) =
  let serialized:t_Array u8 (sz 19) = Rust_primitives.Hax.repeat 0uy (sz 19) in
  let (out, serialized), hax_temp_output:((t_Slice u8 & t_Array u8 (sz 19)) & Prims.unit) =
    match cast (Core.Slice.impl__len #u8 out <: usize) <: u8 with
    | 4uy ->
      let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 28l 0l 28l 0l 28l 0l 28l
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 28l adjacent_2_combined
      in
      let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_2_combined
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 0l 0l 6l 2l 4l 0l
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
        Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_4_combined
      in
      let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
        Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 adjacent_4_combined
          (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 240uy 240uy 240uy 240uy 240uy 240uy 240uy
              240uy 240uy 240uy 240uy 240uy 12uy 4uy 8uy 0uy
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec128)
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
      let out:t_Slice u8 =
        Core.Slice.impl__copy_from_slice #u8
          out
          (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      in
      (out, serialized <: (t_Slice u8 & t_Array u8 (sz 19))), ()
      <:
      ((t_Slice u8 & t_Array u8 (sz 19)) & Prims.unit)
    | 6uy ->
      let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 26l 0l 26l 0l 26l 0l 26l
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 26l adjacent_2_combined
      in
      let adjacent_3_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_2_combined
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
              (-1y) (-1y) (-1y) (-1y) (-1y) 9y 8y 1y 0y (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
              (-1y) (-1y) (-1y) (-1y) (-1y) 9y 8y 1y 0y
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      let adjacent_3_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 adjacent_3_combined
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 1s 1s 1s 1s 1s 1s 1s (1s <<! 4l <: i16)
              1s 1s 1s 1s 1s 1s 1s (1s <<! 4l <: i16)
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      let adjacent_3_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 adjacent_3_combined
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 0l 4l 0l 0l 0l 4l
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      let lower_3_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
        Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_3_combined
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
              lower_3_
            <:
            t_Slice u8)
      in
      let upper_3_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
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
      let out:t_Slice u8 =
        Core.Slice.impl__copy_from_slice #u8
          out
          (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 6 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      in
      (out, serialized <: (t_Slice u8 & t_Array u8 (sz 19))), ()
      <:
      ((t_Slice u8 & t_Array u8 (sz 19)) & Prims.unit)
    | _ ->
      (out, serialized <: (t_Slice u8 & t_Array u8 (sz 19))),
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
      <:
      ((t_Slice u8 & t_Array u8 (sz 19)) & Prims.unit)
  in
  out
