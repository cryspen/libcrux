module Libcrux_ml_kem.Vector.Avx2.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let mulhi_mm256_epi32 (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let prod02:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epu32 lhs rhs
  in
  let prod13:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epu32 (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32
          (mk_i32 245)
          lhs
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 245) rhs
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 (Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi32
        prod02
        prod13
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)
    (Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi32 prod02 prod13
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

let compress_message_coefficient (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let field_modulus_halved:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 ((Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS -!
          mk_i16 1
          <:
          i16) /!
        mk_i16 2
        <:
        i16)
  in
  let field_modulus_quartered:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 ((Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS -!
          mk_i16 1
          <:
          i16) /!
        mk_i16 4
        <:
        i16)
  in
  let shifted:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 field_modulus_halved vector
  in
  let mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 (mk_i32 15) shifted
  in
  let shifted_to_positive:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 mask shifted
  in
  let shifted_to_positive_in_range:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 shifted_to_positive field_modulus_quartered
  in
  Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 (mk_i32 15) shifted_to_positive_in_range

let compress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
     =
  let field_modulus_halved:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (((cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
                <:
                i16)
            <:
            i32) -!
          mk_i32 1
          <:
          i32) /!
        mk_i32 2
        <:
        i32)
  in
  let compression_factor:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 10321340)
  in
  let coefficient_bits_mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 ((mk_i32 1 <<! v_COEFFICIENT_BITS <: i32) -!
        mk_i32 1
        <:
        i32)
  in
  let coefficients_low:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 vector
  in
  let coefficients_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 coefficients_low
  in
  let compressed_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 v_COEFFICIENT_BITS coefficients_low
  in
  let compressed_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 compressed_low field_modulus_halved
  in
  let compressed_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    mulhi_mm256_epi32 compressed_low compression_factor
  in
  let compressed_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 (mk_i32 3) compressed_low
  in
  let compressed_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 compressed_low coefficient_bits_mask
  in
  let coefficients_high:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) vector
  in
  let coefficients_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 coefficients_high
  in
  let compressed_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 v_COEFFICIENT_BITS coefficients_high
  in
  let compressed_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 compressed_high field_modulus_halved
  in
  let compressed_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    mulhi_mm256_epi32 compressed_high compression_factor
  in
  let compressed_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 (mk_i32 3) compressed_high
  in
  let compressed_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 compressed_high coefficient_bits_mask
  in
  let compressed:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_packs_epi32 compressed_low compressed_high
  in
  Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 (mk_i32 216) compressed

let decompress_1_ (a: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let z:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 ()
  in
  let _:Prims.unit =
    assert (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 z == Seq.create 16 (mk_i16 0))
  in
  let _:Prims.unit =
    assert (forall i. Seq.index (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 z) i == mk_i16 0)
  in
  let _:Prims.unit =
    assert (forall i.
          let x = Seq.index (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 a) i in
          ((0 - v x) == 0 \/ (0 - v x) == - 1))
  in
  let _:Prims.unit =
    assert (forall i.
          i < 16 ==>
          Spec.Utils.is_intb (pow2 15 - 1)
            (0 - v (Seq.index (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 a) i)))
  in
  let s:Libcrux_intrinsics.Avx2_extract.t_Vec256 = Libcrux_ml_kem.Vector.Avx2.Arithmetic.sub z a in
  let _:Prims.unit =
    assert (forall i.
          Seq.index (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 s) i == mk_i16 0 \/
          Seq.index (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 s) i == mk_i16 (- 1))
  in
  Libcrux_ml_kem.Vector.Avx2.Arithmetic.bitwise_and_with_constant s (mk_i16 1665)

let decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
     =
  let field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
            <:
            i16)
        <:
        i32)
  in
  let two_pow_coefficient_bits:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 1 <<! v_COEFFICIENT_BITS <: i32)
  in
  let coefficients_low:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 vector
  in
  let coefficients_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 coefficients_low
  in
  let decompressed_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 coefficients_low field_modulus
  in
  let decompressed_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 (mk_i32 1) decompressed_low
  in
  let decompressed_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 decompressed_low two_pow_coefficient_bits
  in
  let decompressed_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 v_COEFFICIENT_BITS decompressed_low
  in
  let decompressed_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 (mk_i32 1) decompressed_low
  in
  let coefficients_high:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) vector
  in
  let coefficients_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 coefficients_high
  in
  let decompressed_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 coefficients_high field_modulus
  in
  let decompressed_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 (mk_i32 1) decompressed_high
  in
  let decompressed_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 decompressed_high two_pow_coefficient_bits
  in
  let decompressed_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 v_COEFFICIENT_BITS decompressed_high
  in
  let decompressed_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 (mk_i32 1) decompressed_high
  in
  let compressed:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_packs_epi32 decompressed_low decompressed_high
  in
  Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 (mk_i32 216) compressed
