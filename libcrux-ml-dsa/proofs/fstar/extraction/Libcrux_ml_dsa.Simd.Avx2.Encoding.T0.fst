module Libcrux_ml_dsa.Simd.Avx2.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let change_interval (simd_unit: Minicore.Core_arch.X86.t_e_ee_m256i) : Minicore.Core_arch.X86.t_e_ee_m256i =
  let interval_end:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1 <<!
        (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! mk_usize 1 <: usize)
        <:
        i32)
  in
  Libcrux_intrinsics.Avx2.mm256_sub_epi32 interval_end simd_unit

let serialize (simd_unit: Minicore.Core_arch.X86.t_e_ee_m256i) (out: t_Slice u8) : t_Slice u8 =
  let serialized:t_Array u8 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16) in
  let simd_unit:Minicore.Core_arch.X86.t_e_ee_m256i = change_interval simd_unit in
  let adjacent_2_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 19)
          (mk_i32 0)
          (mk_i32 19)
          (mk_i32 0)
          (mk_i32 19)
          (mk_i32 0)
          (mk_i32 19)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let adjacent_2_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 19) adjacent_2_combined
  in
  let adjacent_4_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 4)
          (mk_i32 2)
          (mk_i32 0)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let adjacent_4_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 6)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 0)
          (mk_i32 6)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let adjacent_4_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 6) adjacent_4_combined
  in
  let second_4_combined:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_bsrli_epi128 (mk_i32 8) adjacent_4_combined
  in
  let least_12_bits_shifted_up:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_slli_epi64 (mk_i32 52) second_4_combined
  in
  let bits_sequential:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_add_epi64 adjacent_4_combined least_12_bits_shifted_up
  in
  let bits_sequential:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi64 bits_sequential
      (Libcrux_intrinsics.Avx2.mm256_set_epi64x (mk_i64 0) (mk_i64 0) (mk_i64 12) (mk_i64 0)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let bits_sequential:Minicore.Core_arch.X86.t_e_ee_m128i =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 bits_sequential
  in
  let serialized:t_Array u8 (mk_usize 16) =
    Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 serialized bits_sequential
  in
  let out:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      out
      (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 13 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let deserialize__v_COEFFICIENT_MASK: i32 = (mk_i32 1 <<! mk_i32 13 <: i32) -! mk_i32 1

let deserialize (serialized: t_Slice u8) (out: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 serialized, mk_usize 13 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let serialized_extended:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16)
  in
  let serialized_extended:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized_extended
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 13 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized_extended.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 13
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          serialized
        <:
        t_Slice u8)
  in
  let serialized:Minicore.Core_arch.X86.t_e_ee_m128i =
    Libcrux_intrinsics.Avx2.mm_loadu_si128 (serialized_extended <: t_Slice u8)
  in
  let serialized:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set_m128i serialized serialized
  in
  let coefficients:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 serialized
      (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 11)
          (mk_i8 (-1)) (mk_i8 11) (mk_i8 10) (mk_i8 9) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 9) (mk_i8 8)
          (mk_i8 (-1)) (mk_i8 8) (mk_i8 7) (mk_i8 6) (mk_i8 (-1)) (mk_i8 6) (mk_i8 5) (mk_i8 4)
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 4) (mk_i8 3) (mk_i8 (-1)) (mk_i8 3) (mk_i8 2) (mk_i8 1)
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 1) (mk_i8 0)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let coefficients:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 3)
          (mk_i32 6)
          (mk_i32 1)
          (mk_i32 4)
          (mk_i32 7)
          (mk_i32 2)
          (mk_i32 5)
          (mk_i32 0)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let coefficients:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize__v_COEFFICIENT_MASK
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let out:Minicore.Core_arch.X86.t_e_ee_m256i = change_interval coefficients in
  out
