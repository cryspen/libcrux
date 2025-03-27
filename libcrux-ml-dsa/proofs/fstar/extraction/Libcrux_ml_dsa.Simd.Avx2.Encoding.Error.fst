module Libcrux_ml_dsa.Simd.Avx2.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let serialize_when_eta_is_2___v_ETA: i32 = mk_i32 2

let serialize_when_eta_is_2_ (simd_unit: Minicore.Core_arch.X86.t_e_ee_m256i) (out: t_Slice u8)
    : t_Slice u8 =
  let serialized:t_Array u8 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16) in
  let simd_unit_shifted:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 serialize_when_eta_is_2___v_ETA

        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
      simd_unit
  in
  let adjacent_2_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit_shifted
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 29)
          (mk_i32 0)
          (mk_i32 29)
          (mk_i32 0)
          (mk_i32 29)
          (mk_i32 0)
          (mk_i32 29)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let adjacent_2_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 29) adjacent_2_combined
  in
  let adjacent_4_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 8) (mk_i8 (-1)) (mk_i8 0) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 8) (mk_i8 (-1)) (mk_i8 0)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let adjacent_4_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_madd_epi16 adjacent_4_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi16 (mk_i16 0) (mk_i16 0) (mk_i16 0) (mk_i16 0)
          (mk_i16 0) (mk_i16 0) (mk_i16 1 <<! mk_i32 6 <: i16) (mk_i16 1) (mk_i16 0) (mk_i16 0)
          (mk_i16 0) (mk_i16 0) (mk_i16 0) (mk_i16 0) (mk_i16 1 <<! mk_i32 6 <: i16) (mk_i16 1)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let adjacent_6_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_permutevar8x32_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let adjacent_6_combined:Minicore.Core_arch.X86.t_e_ee_m128i =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 adjacent_6_combined
  in
  let adjacent_6_combined:Minicore.Core_arch.X86.t_e_ee_m128i =
    Libcrux_intrinsics.Avx2.mm_sllv_epi32 adjacent_6_combined
      (Libcrux_intrinsics.Avx2.mm_set_epi32 (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 20)
        <:
        Minicore.Core_arch.X86.t_e_ee_m128i)
  in
  let adjacent_6_combined:Minicore.Core_arch.X86.t_e_ee_m128i =
    Libcrux_intrinsics.Avx2.mm_srli_epi64 (mk_i32 20) adjacent_6_combined
  in
  let serialized:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
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
      (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 3 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let serialize_when_eta_is_4___v_ETA: i32 = mk_i32 4

let serialize_when_eta_is_4_ (simd_unit: Minicore.Core_arch.X86.t_e_ee_m256i) (out: t_Slice u8)
    : t_Slice u8 =
  let serialized:t_Array u8 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16) in
  let simd_unit_shifted:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 serialize_when_eta_is_4___v_ETA

        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
      simd_unit
  in
  let adjacent_2_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit_shifted
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 28)
          (mk_i32 0)
          (mk_i32 28)
          (mk_i32 0)
          (mk_i32 28)
          (mk_i32 0)
          (mk_i32 28)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let adjacent_2_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 28) adjacent_2_combined
  in
  let adjacent_4_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 2)
          (mk_i32 4)
          (mk_i32 0)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let adjacent_4_combined:Minicore.Core_arch.X86.t_e_ee_m128i =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 adjacent_4_combined
  in
  let adjacent_4_combined:Minicore.Core_arch.X86.t_e_ee_m128i =
    Libcrux_intrinsics.Avx2.mm_shuffle_epi8 adjacent_4_combined
      (Libcrux_intrinsics.Avx2.mm_set_epi8 (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240)
          (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240)
          (mk_u8 240) (mk_u8 12) (mk_u8 4) (mk_u8 8) (mk_u8 0)
        <:
        Minicore.Core_arch.X86.t_e_ee_m128i)
  in
  let serialized:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
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
      (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 4 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let serialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (simd_unit: Minicore.Core_arch.X86.t_e_ee_m256i)
      (serialized: t_Slice u8)
    : t_Slice u8 =
  let serialized:t_Slice u8 =
    match eta <: Libcrux_ml_dsa.Constants.t_Eta with
    | Libcrux_ml_dsa.Constants.Eta_Two  -> serialize_when_eta_is_2_ simd_unit serialized
    | Libcrux_ml_dsa.Constants.Eta_Four  -> serialize_when_eta_is_4_ simd_unit serialized
  in
  serialized

let deserialize_to_unsigned_when_eta_is_2___v_COEFFICIENT_MASK: i32 =
  (mk_i32 1 <<! mk_i32 3 <: i32) -! mk_i32 1

let deserialize_to_unsigned_when_eta_is_2_ (bytes: t_Slice u8) : Minicore.Core_arch.X86.t_e_ee_m256i =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 3 <: bool)
      in
      ()
  in
  let bytes_in_simd_unit:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set_epi32 (cast (bytes.[ mk_usize 2 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 2 ] <: u8) <: i32)
      (((cast (bytes.[ mk_usize 2 ] <: u8) <: i32) <<! mk_i32 8 <: i32) |.
        (cast (bytes.[ mk_usize 1 ] <: u8) <: i32)
        <:
        i32)
      (cast (bytes.[ mk_usize 1 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 1 ] <: u8) <: i32)
      (((cast (bytes.[ mk_usize 1 ] <: u8) <: i32) <<! mk_i32 8 <: i32) |.
        (cast (bytes.[ mk_usize 0 ] <: u8) <: i32)
        <:
        i32)
      (cast (bytes.[ mk_usize 0 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 0 ] <: u8) <: i32)
  in
  let coefficients:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 bytes_in_simd_unit
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 5)
          (mk_i32 2)
          (mk_i32 7)
          (mk_i32 4)
          (mk_i32 1)
          (mk_i32 6)
          (mk_i32 3)
          (mk_i32 0)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_to_unsigned_when_eta_is_2___v_COEFFICIENT_MASK

      <:
      Minicore.Core_arch.X86.t_e_ee_m256i)

let deserialize_to_unsigned_when_eta_is_4___v_COEFFICIENT_MASK: i32 =
  (mk_i32 1 <<! mk_i32 4 <: i32) -! mk_i32 1

let deserialize_to_unsigned_when_eta_is_4_ (bytes: t_Slice u8) : Minicore.Core_arch.X86.t_e_ee_m256i =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 4 <: bool)
      in
      ()
  in
  let bytes_in_simd_unit:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set_epi32 (cast (bytes.[ mk_usize 3 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 3 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 2 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 2 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 1 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 1 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 0 ] <: u8) <: i32)
      (cast (bytes.[ mk_usize 0 ] <: u8) <: i32)
  in
  let coefficients:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 bytes_in_simd_unit
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 4)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_to_unsigned_when_eta_is_4___v_COEFFICIENT_MASK

      <:
      Minicore.Core_arch.X86.t_e_ee_m256i)

let deserialize_to_unsigned (eta: Libcrux_ml_dsa.Constants.t_Eta) (serialized: t_Slice u8)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  match eta <: Libcrux_ml_dsa.Constants.t_Eta with
  | Libcrux_ml_dsa.Constants.Eta_Two  -> deserialize_to_unsigned_when_eta_is_2_ serialized
  | Libcrux_ml_dsa.Constants.Eta_Four  -> deserialize_to_unsigned_when_eta_is_4_ serialized

let deserialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (serialized: t_Slice u8)
      (out: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  let unsigned:Minicore.Core_arch.X86.t_e_ee_m256i = deserialize_to_unsigned eta serialized in
  let eta:i32 =
    match eta <: Libcrux_ml_dsa.Constants.t_Eta with
    | Libcrux_ml_dsa.Constants.Eta_Two  -> mk_i32 2
    | Libcrux_ml_dsa.Constants.Eta_Four  -> mk_i32 4
  in
  let out:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 eta
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
      unsigned
  in
  out
