module Libcrux_ml_dsa.Simd.Avx2.Encoding.T1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let serialize (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 out <: usize) =. sz 10 <: bool)
      in
      ()
  in
  let serialized:t_Array u8 (sz 24) = Rust_primitives.Hax.repeat 0uy (sz 24) in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 22l 0l 22l 0l 22l 0l 22l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 22l adjacent_2_combined
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 6l 4l 0l 0l 2l 0l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 12l 0l 12l 0l 12l 0l 12l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 12l adjacent_4_combined
  in
  let lower_4_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_4_combined
  in
  let serialized:t_Array u8 (sz 24) =
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
          lower_4_
        <:
        t_Slice u8)
  in
  let upper_4_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l adjacent_4_combined
  in
  let serialized:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 21 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = sz 5;
                Core.Ops.Range.f_end = sz 21
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_4_
        <:
        t_Slice u8)
  in
  let out:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      out
      (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 10 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let deserialize (bytes: t_Slice u8) (out: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 bytes, sz 10 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let bytes_extended:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let bytes_extended:t_Array u8 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes_extended
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 10 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (bytes_extended.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 10 }
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
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) (-1y) 9y 8y (-1y) (-1y) 8y 7y (-1y)
          (-1y) 7y 6y (-1y) (-1y) 6y 5y (-1y) (-1y) 4y 3y (-1y) (-1y) 3y 2y (-1y) (-1y) 2y 1y (-1y)
          (-1y) 1y 0y
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 6l 4l 2l 0l 6l 4l 2l 0l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize__COEFFICIENT_MASK
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  out
