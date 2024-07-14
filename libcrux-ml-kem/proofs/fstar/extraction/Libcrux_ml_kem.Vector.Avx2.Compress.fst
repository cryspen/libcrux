module Libcrux_ml_kem.Vector.Avx2.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let mulhi_mm256_epi32 (lhs rhs: u8) =
  let prod02:u8 = Libcrux_intrinsics.Avx2_extract.mm256_mul_epu32 lhs rhs in
  let prod13:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epu32 (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32
          245l
          lhs
        <:
        u8)
      (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l rhs <: u8)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 (Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi32
        prod02
        prod13
      <:
      u8)
    (Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi32 prod02 prod13 <: u8)

let compress_ciphertext_coefficient (v_COEFFICIENT_BITS: i32) (vector: u8) =
  let field_modulus_halved:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (((cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
                <:
                i16)
            <:
            i32) -!
          1l
          <:
          i32) /!
        2l
        <:
        i32)
  in
  let compression_factor:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 10321340l in
  let coefficient_bits_mask:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 ((1l <<! v_COEFFICIENT_BITS <: i32) -! 1l
        <:
        i32)
  in
  let coefficients_low:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 vector in
  let coefficients_low:u8 = Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 coefficients_low in
  let compressed_low:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 v_COEFFICIENT_BITS coefficients_low
  in
  let compressed_low:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 compressed_low field_modulus_halved
  in
  let compressed_low:u8 = mulhi_mm256_epi32 compressed_low compression_factor in
  let compressed_low:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 3l compressed_low in
  let compressed_low:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 compressed_low coefficient_bits_mask
  in
  let coefficients_high:u8 = Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l vector in
  let coefficients_high:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 coefficients_high
  in
  let compressed_high:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 v_COEFFICIENT_BITS coefficients_high
  in
  let compressed_high:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 compressed_high field_modulus_halved
  in
  let compressed_high:u8 = mulhi_mm256_epi32 compressed_high compression_factor in
  let compressed_high:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 3l compressed_high in
  let compressed_high:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 compressed_high coefficient_bits_mask
  in
  let compressed:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_packs_epi32 compressed_low compressed_high
  in
  Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 216l compressed

let compress_message_coefficient (vector: u8) =
  let field_modulus_halved:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 ((Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS -!
          1s
          <:
          i16) /!
        2s
        <:
        i16)
  in
  let field_modulus_quartered:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 ((Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS -!
          1s
          <:
          i16) /!
        4s
        <:
        i16)
  in
  let shifted:u8 = Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 field_modulus_halved vector in
  let mask:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 15l shifted in
  let shifted_to_positive:u8 = Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 mask shifted in
  let shifted_to_positive_in_range:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 shifted_to_positive field_modulus_quartered
  in
  Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 15l shifted_to_positive_in_range

let decompress_ciphertext_coefficient (v_COEFFICIENT_BITS: i32) (vector: u8) =
  let field_modulus:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
            <:
            i16)
        <:
        i32)
  in
  let two_pow_coefficient_bits:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (1l <<! v_COEFFICIENT_BITS <: i32)
  in
  let coefficients_low:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 vector in
  let coefficients_low:u8 = Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 coefficients_low in
  let decompressed_low:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 coefficients_low field_modulus
  in
  let decompressed_low:u8 = Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 1l decompressed_low in
  let decompressed_low:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 decompressed_low two_pow_coefficient_bits
  in
  let decompressed_low:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 v_COEFFICIENT_BITS decompressed_low
  in
  let decompressed_low:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 1l decompressed_low in
  let coefficients_high:u8 = Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l vector in
  let coefficients_high:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 coefficients_high
  in
  let decompressed_high:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 coefficients_high field_modulus
  in
  let decompressed_high:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 1l decompressed_high
  in
  let decompressed_high:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 decompressed_high two_pow_coefficient_bits
  in
  let decompressed_high:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 v_COEFFICIENT_BITS decompressed_high
  in
  let decompressed_high:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 1l decompressed_high
  in
  let compressed:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_packs_epi32 decompressed_low decompressed_high
  in
  Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 216l compressed
