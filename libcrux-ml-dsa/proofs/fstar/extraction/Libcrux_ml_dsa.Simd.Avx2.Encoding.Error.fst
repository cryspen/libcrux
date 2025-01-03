module Libcrux_ml_dsa.Simd.Avx2.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_to_unsigned_when_eta_is_2_ (bytes: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 bytes <: usize) =. sz 3 <: bool)
      in
      ()
  in
  let bytes_in_simd_unit:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (cast (bytes.[ sz 2 ] <: u8) <: i32)
      (cast (bytes.[ sz 2 ] <: u8) <: i32)
      (((cast (bytes.[ sz 2 ] <: u8) <: i32) <<! 8l <: i32) |. (cast (bytes.[ sz 1 ] <: u8) <: i32)
        <:
        i32)
      (cast (bytes.[ sz 1 ] <: u8) <: i32)
      (cast (bytes.[ sz 1 ] <: u8) <: i32)
      (((cast (bytes.[ sz 1 ] <: u8) <: i32) <<! 8l <: i32) |. (cast (bytes.[ sz 0 ] <: u8) <: i32)
        <:
        i32)
      (cast (bytes.[ sz 0 ] <: u8) <: i32)
      (cast (bytes.[ sz 0 ] <: u8) <: i32)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 bytes_in_simd_unit
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 5l 2l 7l 4l 1l 6l 3l 0l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize_to_unsigned_when_eta_is_2___COEFFICIENT_MASK

      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

let deserialize_to_unsigned_when_eta_is_4_ (bytes: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 bytes <: usize) =. sz 4 <: bool)
      in
      ()
  in
  let bytes_in_simd_unit:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (cast (bytes.[ sz 3 ] <: u8) <: i32)
      (cast (bytes.[ sz 3 ] <: u8) <: i32)
      (cast (bytes.[ sz 2 ] <: u8) <: i32)
      (cast (bytes.[ sz 2 ] <: u8) <: i32)
      (cast (bytes.[ sz 1 ] <: u8) <: i32)
      (cast (bytes.[ sz 1 ] <: u8) <: i32)
      (cast (bytes.[ sz 0 ] <: u8) <: i32)
      (cast (bytes.[ sz 0 ] <: u8) <: i32)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 bytes_in_simd_unit
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 4l 0l 4l 0l 4l 0l 4l 0l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize_to_unsigned_when_eta_is_4___COEFFICIENT_MASK

      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

let deserialize_to_unsigned (eta: Libcrux_ml_dsa.Constants.t_Eta) (serialized: t_Slice u8) =
  match eta <: Libcrux_ml_dsa.Constants.t_Eta with
  | Libcrux_ml_dsa.Constants.Eta_Two  -> deserialize_to_unsigned_when_eta_is_2_ serialized
  | Libcrux_ml_dsa.Constants.Eta_Four  -> deserialize_to_unsigned_when_eta_is_4_ serialized

let deserialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (serialized: t_Slice u8)
      (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
     =
  let unsigned:Libcrux_intrinsics.Avx2_extract.t_Vec256 = deserialize_to_unsigned eta serialized in
  let out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          (cast (Libcrux_ml_dsa.Constants.t_Eta_cast_to_repr eta <: isize) <: i32)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      unsigned
  in
  out

let serialize_when_eta_is_2_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice u8) =
  let serialized:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let simd_unit_shifted:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          serialize_when_eta_is_2___ETA
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      simd_unit
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit_shifted
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 29l 0l 29l 0l 29l 0l 29l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 29l adjacent_2_combined
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) 8y (-1y) 0y (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) 8y (-1y) 0y
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_madd_epi16 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 0s 0s 0s 0s 0s 0s (1s <<! 6l <: i16) 1s 0s 0s
          0s 0s 0s 0s (1s <<! 6l <: i16) 1s
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_6_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 0l 0l 0l 0l 4l 0l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_6_combined:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_6_combined
  in
  let adjacent_6_combined:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_sllv_epi32 adjacent_6_combined
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi32 0l 0l 0l 20l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let adjacent_6_combined:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_srli_epi64 20l adjacent_6_combined
  in
  let serialized:t_Array u8 (sz 16) =
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
          adjacent_6_combined
        <:
        t_Slice u8)
  in
  let out:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      out
      (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 3 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let serialize_when_eta_is_4_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice u8) =
  let serialized:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let simd_unit_shifted:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          serialize_when_eta_is_4___ETA
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      simd_unit
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit_shifted
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
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 240uy 240uy 240uy 240uy 240uy 240uy 240uy 240uy
          240uy 240uy 240uy 240uy 12uy 4uy 8uy 0uy
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let serialized:t_Array u8 (sz 16) =
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
  let hax_temp_output, out:(Prims.unit & t_Slice u8) =
    (),
    Core.Slice.impl__copy_from_slice #u8
      out
      (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
    <:
    (Prims.unit & t_Slice u8)
  in
  out

let serialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (serialized: t_Slice u8)
     =
  let serialized, hax_temp_output:(t_Slice u8 & Prims.unit) =
    match eta <: Libcrux_ml_dsa.Constants.t_Eta with
    | Libcrux_ml_dsa.Constants.Eta_Two  ->
      serialize_when_eta_is_2_ simd_unit serialized, () <: (t_Slice u8 & Prims.unit)
    | Libcrux_ml_dsa.Constants.Eta_Four  ->
      serialize_when_eta_is_4_ simd_unit serialized, () <: (t_Slice u8 & Prims.unit)
  in
  serialized
