module Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_when_gamma1_is_2_pow_17_ (serialized: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =.
            Rust_primitives.mk_usize 18
            <:
            bool)
      in
      ()
  in
  let serialized_lower:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (serialized.[ {
            Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
            Core.Ops.Range.f_end = Rust_primitives.mk_usize 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let serialized_upper:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (serialized.[ {
            Core.Ops.Range.f_start = Rust_primitives.mk_usize 2;
            Core.Ops.Range.f_end = Rust_primitives.mk_usize 18
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let serialized:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_m128i serialized_upper serialized_lower
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 serialized
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 15) (Rust_primitives.mk_i8 14) (Rust_primitives.mk_i8 13)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 13) (Rust_primitives.mk_i8 12)
          (Rust_primitives.mk_i8 11) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 11)
          (Rust_primitives.mk_i8 10) (Rust_primitives.mk_i8 9) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 9) (Rust_primitives.mk_i8 8) (Rust_primitives.mk_i8 7)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 8) (Rust_primitives.mk_i8 7)
          (Rust_primitives.mk_i8 6) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 6)
          (Rust_primitives.mk_i8 5) (Rust_primitives.mk_i8 4) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 4) (Rust_primitives.mk_i8 3) (Rust_primitives.mk_i8 2)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 2) (Rust_primitives.mk_i8 1)
          (Rust_primitives.mk_i8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 6)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 2)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 6)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 2)
          (Rust_primitives.mk_i32 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_MASK

        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_17___GAMMA1

      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)
    coefficients

let deserialize_when_gamma1_is_2_pow_19_ (serialized: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =.
            Rust_primitives.mk_usize 20
            <:
            bool)
      in
      ()
  in
  let serialized_lower:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (serialized.[ {
            Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
            Core.Ops.Range.f_end = Rust_primitives.mk_usize 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let serialized_upper:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (serialized.[ {
            Core.Ops.Range.f_start = Rust_primitives.mk_usize 4;
            Core.Ops.Range.f_end = Rust_primitives.mk_usize 20
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let serialized:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_m128i serialized_upper serialized_lower
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 serialized
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 15) (Rust_primitives.mk_i8 14) (Rust_primitives.mk_i8 13)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 13) (Rust_primitives.mk_i8 12)
          (Rust_primitives.mk_i8 11) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 10)
          (Rust_primitives.mk_i8 9) (Rust_primitives.mk_i8 8) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 8) (Rust_primitives.mk_i8 7) (Rust_primitives.mk_i8 6)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 9) (Rust_primitives.mk_i8 8)
          (Rust_primitives.mk_i8 7) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 7)
          (Rust_primitives.mk_i8 6) (Rust_primitives.mk_i8 5) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 4) (Rust_primitives.mk_i8 3) (Rust_primitives.mk_i8 2)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 2) (Rust_primitives.mk_i8 1)
          (Rust_primitives.mk_i8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 4)
          (Rust_primitives.mk_i32 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_19___GAMMA1_TIMES_2_MASK

        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_19___GAMMA1

      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)
    coefficients

let deserialize (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) =
  match cast (v_GAMMA1_EXPONENT <: usize) <: u8 with
  | 17 -> deserialize_when_gamma1_is_2_pow_17_ serialized
  | 19 -> deserialize_when_gamma1_is_2_pow_19_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let serialize_when_gamma1_is_2_pow_17_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
     =
  let serialized:t_Array u8 (Rust_primitives.mk_usize 32) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 32)
  in
  let simd_unit_shifted:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          serialize_when_gamma1_is_2_pow_17___GAMMA1
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      simd_unit
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit_shifted
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 14)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 14)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 14)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 14)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (Rust_primitives.mk_i32 14) adjacent_2_combined
  in
  let every_second_element:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_bsrli_epi128 (Rust_primitives.mk_i32 8)
      adjacent_2_combined
  in
  let every_second_element_shifted:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi64 (Rust_primitives.mk_i32 36)
      every_second_element
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi64 adjacent_2_combined every_second_element_shifted
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi64 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi64x (Rust_primitives.mk_i64 28)
          (Rust_primitives.mk_i64 0)
          (Rust_primitives.mk_i64 28)
          (Rust_primitives.mk_i64 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let lower_4_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_4_combined
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
          Core.Ops.Range.f_end = Rust_primitives.mk_usize 16
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
                Core.Ops.Range.f_end = Rust_primitives.mk_usize 16
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
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (Rust_primitives.mk_i32 1)
      adjacent_4_combined
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 9;
          Core.Ops.Range.f_end = Rust_primitives.mk_usize 25
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 9;
                Core.Ops.Range.f_end = Rust_primitives.mk_usize 25
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_4_
        <:
        t_Slice u8)
  in
  Core.Result.impl__unwrap #(t_Array u8 v_OUTPUT_SIZE)
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 v_OUTPUT_SIZE)
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ {
              Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
              Core.Ops.Range.f_end = Rust_primitives.mk_usize 18
            }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 v_OUTPUT_SIZE) Core.Array.t_TryFromSliceError)

let serialize_when_gamma1_is_2_pow_19_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
     =
  let serialized:t_Array u8 (Rust_primitives.mk_usize 32) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 32)
  in
  let simd_unit_shifted:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
          serialize_when_gamma1_is_2_pow_19___GAMMA1
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      simd_unit
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit_shifted
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 12)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 12)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 12)
          (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_i32 12)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (Rust_primitives.mk_i32 12) adjacent_2_combined
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 12)
          (Rust_primitives.mk_i8 11) (Rust_primitives.mk_i8 10) (Rust_primitives.mk_i8 9)
          (Rust_primitives.mk_i8 8) (Rust_primitives.mk_i8 4) (Rust_primitives.mk_i8 3)
          (Rust_primitives.mk_i8 2) (Rust_primitives.mk_i8 1) (Rust_primitives.mk_i8 0)
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1)) (Rust_primitives.mk_i8 (-1))
          (Rust_primitives.mk_i8 12) (Rust_primitives.mk_i8 11) (Rust_primitives.mk_i8 10)
          (Rust_primitives.mk_i8 9) (Rust_primitives.mk_i8 8) (Rust_primitives.mk_i8 4)
          (Rust_primitives.mk_i8 3) (Rust_primitives.mk_i8 2) (Rust_primitives.mk_i8 1)
          (Rust_primitives.mk_i8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let lower_4_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_4_combined
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
          Core.Ops.Range.f_end = Rust_primitives.mk_usize 16
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
                Core.Ops.Range.f_end = Rust_primitives.mk_usize 16
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
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (Rust_primitives.mk_i32 1)
      adjacent_4_combined
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 10;
          Core.Ops.Range.f_end = Rust_primitives.mk_usize 26
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 10;
                Core.Ops.Range.f_end = Rust_primitives.mk_usize 26
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_4_
        <:
        t_Slice u8)
  in
  Core.Result.impl__unwrap #(t_Array u8 v_OUTPUT_SIZE)
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 v_OUTPUT_SIZE)
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ {
              Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
              Core.Ops.Range.f_end = Rust_primitives.mk_usize 20
            }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 v_OUTPUT_SIZE) Core.Array.t_TryFromSliceError)

let serialize (v_OUTPUT_SIZE: usize) (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  match cast (v_OUTPUT_SIZE <: usize) <: u8 with
  | 18 -> serialize_when_gamma1_is_2_pow_17_ v_OUTPUT_SIZE simd_unit
  | 20 -> serialize_when_gamma1_is_2_pow_19_ v_OUTPUT_SIZE simd_unit
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
