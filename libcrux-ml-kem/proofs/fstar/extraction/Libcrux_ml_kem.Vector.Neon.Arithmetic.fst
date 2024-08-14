module Libcrux_ml_kem.Vector.Neon.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let barrett_reduce_int16x8_t (v: u8) =
  let adder:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 1024s in
  let vec:u8 = Libcrux_intrinsics.Arm64_extract.v__vqdmulhq_n_s16 v v_BARRETT_MULTIPLIER in
  let vec:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 vec adder in
  let quotient:u8 = Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 11l vec in
  let sub:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vmulq_n_s16 quotient
      Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 v sub

let montgomery_reduce_int16x8_t (low high: u8) =
  let k:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 (Libcrux_intrinsics.Arm64_extract.v__vmulq_n_u16
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_s16 low <: u8)
          (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R <: u32) <: u16)
        <:
        u8)
  in
  let c:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 1l
      (Libcrux_intrinsics.Arm64_extract.v__vqdmulhq_n_s16 k
          Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        u8)
  in
  Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 high c

let montgomery_multiply_by_constant_int16x8_t (v: u8) (c: i16) =
  let vv_low:u8 = Libcrux_intrinsics.Arm64_extract.v__vmulq_n_s16 v c in
  let vv_high:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 1l
      (Libcrux_intrinsics.Arm64_extract.v__vqdmulhq_n_s16 v c <: u8)
  in
  montgomery_reduce_int16x8_t vv_low vv_high

let montgomery_multiply_int16x8_t (v c: u8) =
  let vv_low:u8 = Libcrux_intrinsics.Arm64_extract.v__vmulq_s16 v c in
  let vv_high:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 1l
      (Libcrux_intrinsics.Arm64_extract.v__vqdmulhq_s16 v c <: u8)
  in
  montgomery_reduce_int16x8_t vv_low vv_high

let add (lhs rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let lhs:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      lhs with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 lhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        rhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let lhs:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      lhs with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 lhs
          .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        rhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  lhs

let barrett_reduce (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      barrett_reduce_int16x8_t v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      barrett_reduce_int16x8_t v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let bitwise_and_with_constant (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (c: i16) =
  let c:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 c in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vandq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low c
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vandq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        c
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let cond_subtract_3329_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let c:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 3329s in
  let m0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vcgeq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low c
  in
  let m1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vcgeq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high c
  in
  let c0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_s16 c
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 m0 <: u8)
  in
  let c1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_s16 c
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 m1 <: u8)
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        c0
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        c1
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let montgomery_multiply_by_constant
      (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (c: i16)
     =
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      montgomery_multiply_by_constant_int16x8_t v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low c
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      montgomery_multiply_by_constant_int16x8_t v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high c
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let multiply_by_constant (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (c: i16) =
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vmulq_n_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        c
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vmulq_n_s16 v
          .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        c
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let shift_right (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 v_SHIFT_BY
        v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 v_SHIFT_BY
        v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let sub (lhs rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let lhs:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      lhs with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 lhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        rhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let lhs:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      lhs with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 lhs
          .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        rhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  lhs
