module Libcrux_ml_kem.Vector.Neon.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let compress_int32x4_t (v_COEFFICIENT_BITS: i32) (v: u8) =
  let half:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_u32 (mk_u32 1664) in
  let compressed:u8 = Libcrux_intrinsics.Arm64_extract.v__vshlq_n_u32 v_COEFFICIENT_BITS v in
  let compressed:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_u32 compressed half in
  let compressed:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s32 (Libcrux_intrinsics.Arm64_extract.v__vqdmulhq_n_s32
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_u32 compressed <: u8)
          (mk_i32 10321340)
        <:
        u8)
  in
  Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 (mk_i32 4) compressed

let mask_n_least_significant_bits (coefficient_bits: i16) =
  match coefficient_bits <: i16 with
  | Rust_primitives.Integers.MkInt 4 -> mk_i16 15
  | Rust_primitives.Integers.MkInt 5 -> mk_i16 31
  | Rust_primitives.Integers.MkInt 10 -> mk_i16 1023
  | Rust_primitives.Integers.MkInt 11 -> mk_i16 2047
  | x -> (mk_i16 1 <<! x <: i16) -! mk_i16 1

let compress (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let mask:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 (mask_n_least_significant_bits (cast (v_COEFFICIENT_BITS
                <:
                i32)
            <:
            i16)
        <:
        i16)
  in
  let mask16:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_u32 (mk_u32 65535) in
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_u32 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        <:
        u8)
      mask16
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 (mk_i32 16)
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16 v
            .Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        <:
        u8)
  in
  let high0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_u32 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        <:
        u8)
      mask16
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 (mk_i32 16)
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16 v
            .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        <:
        u8)
  in
  let low0:u8 = compress_int32x4_t v_COEFFICIENT_BITS low0 in
  let low1:u8 = compress_int32x4_t v_COEFFICIENT_BITS low1 in
  let high0:u8 = compress_int32x4_t v_COEFFICIENT_BITS high0 in
  let high1:u8 = compress_int32x4_t v_COEFFICIENT_BITS high1 in
  let low:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32
          low0
        <:
        u8)
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32 low1 <: u8)
  in
  let high:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32
          high0
        <:
        u8)
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32 high1 <: u8)
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vandq_s16 low mask
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vandq_s16 high mask
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let compress_1_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let half:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 (mk_i16 1664) in
  let quarter:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 (mk_i16 832) in
  let shifted:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 half
      v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
  in
  let mask:u8 = Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 (mk_i32 15) shifted in
  let shifted_to_positive:u8 = Libcrux_intrinsics.Arm64_extract.v__veorq_s16 mask shifted in
  let shifted_positive_in_range:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 shifted_to_positive quarter
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 (Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u16
            (mk_i32 15)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_s16 shifted_positive_in_range
              <:
              u8)
          <:
          u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let shifted:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 half
      v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
  in
  let mask:u8 = Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 (mk_i32 15) shifted in
  let shifted_to_positive:u8 = Libcrux_intrinsics.Arm64_extract.v__veorq_s16 mask shifted in
  let shifted_positive_in_range:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 shifted_to_positive quarter
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 (Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u16
            (mk_i32 15)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_s16 shifted_positive_in_range
              <:
              u8)
          <:
          u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let decompress_uint32x4_t (v_COEFFICIENT_BITS: i32) (v: u8) =
  let coeff:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vdupq_n_u32 (mk_u32 1 <<!
        (v_COEFFICIENT_BITS -! mk_i32 1 <: i32)
        <:
        u32)
  in
  let decompressed:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vmulq_n_u32 v
      (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: u32)
  in
  let decompressed:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_u32 decompressed coeff in
  Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 v_COEFFICIENT_BITS decompressed

let decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
     =
  let mask16:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_u32 (mk_u32 65535) in
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_u32 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        <:
        u8)
      mask16
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 (mk_i32 16)
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16 v
            .Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        <:
        u8)
  in
  let high0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_u32 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        <:
        u8)
      mask16
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 (mk_i32 16)
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16 v
            .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        <:
        u8)
  in
  let low0:u8 = decompress_uint32x4_t v_COEFFICIENT_BITS low0 in
  let low1:u8 = decompress_uint32x4_t v_COEFFICIENT_BITS low1 in
  let high0:u8 = decompress_uint32x4_t v_COEFFICIENT_BITS high0 in
  let high1:u8 = decompress_uint32x4_t v_COEFFICIENT_BITS high1 in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32
            low0
          <:
          u8)
        (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32 low1 <: u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32
            high0
          <:
          u8)
        (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32 high1 <: u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v
