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
  let bytes_in_simd_unit:u8 =
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
  let coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 bytes_in_simd_unit
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 5l 2l 7l 4l 1l 6l 3l 0l <: u8)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize_to_unsigned_when_eta_is_2___COEFFICIENT_MASK

      <:
      u8)

let deserialize_to_unsigned_when_eta_is_4_ (bytes: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 bytes <: usize) =. sz 4 <: bool)
      in
      ()
  in
  let bytes_in_simd_unit:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (cast (bytes.[ sz 3 ] <: u8) <: i32)
      (cast (bytes.[ sz 3 ] <: u8) <: i32)
      (cast (bytes.[ sz 2 ] <: u8) <: i32)
      (cast (bytes.[ sz 2 ] <: u8) <: i32)
      (cast (bytes.[ sz 1 ] <: u8) <: i32)
      (cast (bytes.[ sz 1 ] <: u8) <: i32)
      (cast (bytes.[ sz 0 ] <: u8) <: i32)
      (cast (bytes.[ sz 0 ] <: u8) <: i32)
  in
  let coefficients:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 bytes_in_simd_unit
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 4l 0l 4l 0l 4l 0l 4l 0l <: u8)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize_to_unsigned_when_eta_is_4___COEFFICIENT_MASK

      <:
      u8)

let deserialize_to_unsigned (v_ETA: usize) (serialized: t_Slice u8) =
  match cast (v_ETA <: usize) <: u8 with
  | 2uy -> deserialize_to_unsigned_when_eta_is_2_ serialized
  | 4uy -> deserialize_to_unsigned_when_eta_is_4_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize (v_ETA: usize) (serialized: t_Slice u8) =
  let unsigned:u8 = deserialize_to_unsigned v_ETA serialized in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (
          cast (v_ETA <: usize) <: i32)
      <:
      u8)
    unsigned

let serialize_when_eta_is_2_ (v_OUTPUT_SIZE: usize) (simd_unit: u8) =
  let serialized:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let simd_unit_shifted:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          serialize_when_eta_is_2___ETA
        <:
        u8)
      simd_unit
  in
  let adjacent_2_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit_shifted
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 29l 0l 29l 0l 29l 0l 29l <: u8)
  in
  let adjacent_2_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 29l adjacent_2_combined
  in
  let adjacent_4_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) 8y (-1y) 0y (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) 8y (-1y) 0y
        <:
        u8)
  in
  let adjacent_4_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_madd_epi16 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 0s 0s 0s 0s 0s 0s (1s <<! 6l <: i16) 1s 0s 0s
          0s 0s 0s 0s (1s <<! 6l <: i16) 1s
        <:
        u8)
  in
  let adjacent_6_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 0l 0l 0l 0l 4l 0l <: u8)
  in
  let adjacent_6_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_6_combined
  in
  let adjacent_6_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm_sllv_epi32 adjacent_6_combined
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi32 0l 0l 0l 20l <: u8)
  in
  let adjacent_6_combined:u8 =
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
  Core.Result.impl__unwrap #(t_Array u8 v_OUTPUT_SIZE)
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 v_OUTPUT_SIZE)
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 3 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 v_OUTPUT_SIZE) Core.Array.t_TryFromSliceError)

let serialize_when_eta_is_4_ (v_OUTPUT_SIZE: usize) (simd_unit: u8) =
  let serialized:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let simd_unit_shifted:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          serialize_when_eta_is_4___ETA
        <:
        u8)
      simd_unit
  in
  let adjacent_2_combined:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit_shifted
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

let serialize (v_OUTPUT_SIZE: usize) (simd_unit: u8) =
  match cast (v_OUTPUT_SIZE <: usize) <: u8 with
  | 3uy -> serialize_when_eta_is_2_ v_OUTPUT_SIZE simd_unit
  | 4uy -> serialize_when_eta_is_4_ v_OUTPUT_SIZE simd_unit
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
