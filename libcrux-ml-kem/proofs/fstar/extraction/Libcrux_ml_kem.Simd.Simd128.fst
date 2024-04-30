module Libcrux_ml_kem.Simd.Simd128
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let mask_n_least_significant_bits (coefficient_bits: i32) =
  match coefficient_bits with
  | 4l -> 15l
  | 5l -> 31l
  | 10l -> 1023l
  | 11l -> 2047l
  | x -> (1l <<! x <: i32) -! 1l

let montgomery_reduce_i32x2_t (v: Core.Core_arch.Arm_shared.Neon.t_int32x2_t) =
  let m:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdup_n_s32 65535l
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vand_s32 v m
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmul_n_s32 t0 v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int16x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vreinterpret_s16_s32 t0
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_n_s16 t0
      (cast (Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) <: i16)
  in
  let c0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 16l t0
  in
  let c0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s64 (Libcrux_ml_kem.Simd.Simd128.Neon.vreinterpretq_s64_s32
          c0
        <:
        Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
  in
  let v0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshr_n_s32 16l v
  in
  Libcrux_ml_kem.Simd.Simd128.Neon.vsub_s32 v0 c0

let montgomery_reduce_i32x4_t (v: Core.Core_arch.Arm_shared.Neon.t_int32x4_t) =
  let m:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 65535l
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 v m
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_n_s32 t0 v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmovl_s16 (Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s32 t0
        <:
        Core.Core_arch.Arm_shared.Neon.t_int16x4_t)
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_n_s32 t0 Libcrux_ml_kem.Constants.v_FIELD_MODULUS
  in
  let c0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 16l t0
  in
  let v0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 16l v
  in
  Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 v0 c0

let v_ZERO (_: Prims.unit) =
  {
    f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 0l;
    f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 0l
  }
  <:
  t_SIMD128Vector

let add_constant (v: t_SIMD128Vector) (c: i32) =
  let c:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 c
  in
  {
    f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s32 v.f_low c;
    f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s32 v.f_high c
  }
  <:
  t_SIMD128Vector

let add_vec (lhs rhs: t_SIMD128Vector) =
  {
    f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s32 lhs.f_low rhs.f_low;
    f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s32 lhs.f_high rhs.f_high
  }
  <:
  t_SIMD128Vector

let barrett_reduce (v: t_SIMD128Vector) =
  let adder:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s64 33554432L
  in
  let low0:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_n_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vget_low_s32 v
            .f_low
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
      v_BARRETT_MULTIPLIER
  in
  let high0:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_n_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vget_low_s32 v
            .f_high
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
      v_BARRETT_MULTIPLIER
  in
  let low1:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_high_n_s32 v.f_low v_BARRETT_MULTIPLIER
  in
  let high1:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_high_n_s32 v.f_high v_BARRETT_MULTIPLIER
  in
  let low0:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s64 26l
      (Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s64 low0 adder
        <:
        Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
  in
  let low1:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s64 26l
      (Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s64 low1 adder
        <:
        Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
  in
  let high0:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s64 26l
      (Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s64 high0 adder
        <:
        Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
  in
  let high1:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s64 26l
      (Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s64 high1 adder
        <:
        Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
  in
  let low:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vcombine_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s64 low0
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
      (Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s64 low1 <: Core.Core_arch.Arm_shared.Neon.t_int32x2_t
      )
  in
  let high:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vcombine_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s64 high0
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
      (Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s64 high1
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
  in
  let low:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_n_s32 low 3329l
  in
  let high:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_n_s32 high 3329l
  in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 v.f_low low } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 v.f_high high } <: t_SIMD128Vector
  in
  v

let bitwise_and_with_constant (v: t_SIMD128Vector) (c: i32) =
  let c:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 c
  in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 v.f_low c } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 v.f_high c } <: t_SIMD128Vector
  in
  v

let compress (v_COEFFICIENT_BITS: i32) (v: t_SIMD128Vector) =
  let half:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 1664l
  in
  let low:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshlq_n_s32 v_COEFFICIENT_BITS v.f_low
  in
  let high:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshlq_n_s32 v_COEFFICIENT_BITS v.f_high
  in
  let low:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s32 low half
  in
  let high:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s32 high half
  in
  let low0:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_n_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vget_low_s32 low
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
      10321340l
  in
  let high0:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_n_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vget_low_s32 high
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
      10321340l
  in
  let low1:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_high_n_s32 low 10321340l
  in
  let high1:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_high_n_s32 high 10321340l
  in
  let low0:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s64 35l low0
  in
  let high0:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s64 35l high0
  in
  let low1:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s64 35l low1
  in
  let high1:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s64 35l high1
  in
  let low:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vcombine_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s64 low0
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
      (Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s64 low1 <: Core.Core_arch.Arm_shared.Neon.t_int32x2_t
      )
  in
  let high:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vcombine_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s64 high0
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
      (Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s64 high1
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
  in
  let mask:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 (mask_n_least_significant_bits v_COEFFICIENT_BITS
        <:
        i32)
  in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 low mask } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 high mask } <: t_SIMD128Vector
  in
  v

let compress_1_ (v: t_SIMD128Vector) =
  let half:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 1664l
  in
  let quarter:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 832l
  in
  let shifted0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 half v.f_low
  in
  let shifted1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 half v.f_high
  in
  let mask0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 31l shifted0
  in
  let mask1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 31l shifted1
  in
  let shifted_to_positive0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.veorq_s32 mask0 shifted0
  in
  let shifted_to_positive1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.veorq_s32 mask1 shifted1
  in
  let shifted_positive_in_range0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 shifted_to_positive0 quarter
  in
  let shifted_positive_in_range1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 shifted_to_positive1 quarter
  in
  let v:t_SIMD128Vector =
    {
      v with
      f_low
      =
      Libcrux_ml_kem.Simd.Simd128.Neon.vreinterpretq_s32_u32 (Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_u32
            31l
            (Libcrux_ml_kem.Simd.Simd128.Neon.vreinterpretq_u32_s32 shifted_positive_in_range0
              <:
              Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
          <:
          Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    }
    <:
    t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    {
      v with
      f_high
      =
      Libcrux_ml_kem.Simd.Simd128.Neon.vreinterpretq_s32_u32 (Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_u32
            31l
            (Libcrux_ml_kem.Simd.Simd128.Neon.vreinterpretq_u32_s32 shifted_positive_in_range1
              <:
              Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
          <:
          Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    }
    <:
    t_SIMD128Vector
  in
  v

let cond_subtract_3329_ (v: t_SIMD128Vector) =
  let c:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 3329l
  in
  let m0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vcgeq_s32_reinterpreted v.f_low c
  in
  let m1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vcgeq_s32_reinterpreted v.f_high c
  in
  let rhs0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 m0 c
  in
  let rhs1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 m1 c
  in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 v.f_low rhs0 } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 v.f_high rhs1 } <: t_SIMD128Vector
  in
  v

let deserialize_1_ (a: u8) =
  let dup:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 (cast (a <: u8) <: i32)
  in
  let (shifter0: t_Array i32 (sz 4)):t_Array i32 (sz 4) =
    let list = [0l; (-1l); (-2l); (-3l)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  let (shifter1: t_Array i32 (sz 4)):t_Array i32 (sz 4) =
    let list = [(-4l); (-5l); (-6l); (-7l)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  let shift0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_s32 (Rust_primitives.unsize shifter0 <: t_Slice i32)
  in
  let shift1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_s32 (Rust_primitives.unsize shifter1 <: t_Slice i32)
  in
  let low:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshlq_s32 dup shift0
  in
  let high:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshlq_s32 dup shift1
  in
  {
    f_low
    =
    Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 low
      (Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 1l <: Core.Core_arch.Arm_shared.Neon.t_int32x4_t
      );
    f_high
    =
    Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 high
      (Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 1l <: Core.Core_arch.Arm_shared.Neon.t_int32x4_t
      )
  }
  <:
  t_SIMD128Vector

let from_i32_array (array: t_Array i32 (sz 8)) =
  {
    f_low
    =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_s32 (array.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 4
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i32);
    f_high
    =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_s32 (array.[ {
            Core.Ops.Range.f_start = sz 4;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i32)
  }
  <:
  t_SIMD128Vector

let inv_ntt_layer_1_step (v: t_SIMD128Vector) (zeta1 zeta2: i32) =
  let low0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vget_low_s32 v.f_low
  in
  let low1:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vget_high_s32 v.f_low
  in
  let high0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vget_low_s32 v.f_high
  in
  let high1:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vget_high_s32 v.f_high
  in
  let low_a_minus_b:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsub_s32 low1 low0
  in
  let high_a_minus_b:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsub_s32 high1 high0
  in
  let low0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vadd_s32 low0 low1
  in
  let high0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vadd_s32 high0 high1
  in
  let low_tmp:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmul_n_s32 low_a_minus_b zeta1
  in
  let high_tmp:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmul_n_s32 high_a_minus_b zeta2
  in
  let low1:Core.Core_arch.Arm_shared.Neon.t_int32x2_t = montgomery_reduce_i32x2_t low_tmp in
  let high1:Core.Core_arch.Arm_shared.Neon.t_int32x2_t = montgomery_reduce_i32x2_t high_tmp in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vcombine_s32 low0 low1 } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vcombine_s32 high0 high1 } <: t_SIMD128Vector
  in
  v

let inv_ntt_layer_2_step (v: t_SIMD128Vector) (zeta: i32) =
  let tmp:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 v.f_high v.f_low
  in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s32 v.f_low v.f_high }
    <:
    t_SIMD128Vector
  in
  let tmp:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_n_s32 tmp zeta
  in
  let v:t_SIMD128Vector = { v with f_high = montgomery_reduce_i32x4_t tmp } <: t_SIMD128Vector in
  v

let montgomery_reduce (v: t_SIMD128Vector) =
  let m:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vdupq_n_s32 65535l
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 v.f_low m
  in
  let t1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vandq_s32 v.f_high m
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_n_s32 t0 v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
  in
  let t1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_n_s32 t1 v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int16x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s32 t0
  in
  let t0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_n_s16 t0
      (cast (Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) <: i16)
  in
  let t1:Core.Core_arch.Arm_shared.Neon.t_int16x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmovn_s32 t1
  in
  let t1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmull_n_s16 t1
      (cast (Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) <: i16)
  in
  let c0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 16l t0
  in
  let c1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 16l t1
  in
  let v0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 16l v.f_low
  in
  let v1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 16l v.f_high
  in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 v0 c0 } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 v1 c1 } <: t_SIMD128Vector
  in
  v

let multiply_by_constant (v: t_SIMD128Vector) (c: i32) =
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_n_s32 v.f_low c } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_n_s32 v.f_high c } <: t_SIMD128Vector
  in
  v

let ntt_layer_1_step (v: t_SIMD128Vector) (zeta1 zeta2: i32) =
  let low0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vget_low_s32 v.f_low
  in
  let low1:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vget_high_s32 v.f_low
  in
  let high0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vget_low_s32 v.f_high
  in
  let high1:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vget_high_s32 v.f_high
  in
  let low_tmp:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmul_n_s32 low1 zeta1
  in
  let high_tmp:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmul_n_s32 high1 zeta2
  in
  let low_tmp:Core.Core_arch.Arm_shared.Neon.t_int32x2_t = montgomery_reduce_i32x2_t low_tmp in
  let high_tmp:Core.Core_arch.Arm_shared.Neon.t_int32x2_t = montgomery_reduce_i32x2_t high_tmp in
  let low1:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsub_s32 low0 low_tmp
  in
  let high1:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsub_s32 high0 high_tmp
  in
  let low0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vadd_s32 low0 low_tmp
  in
  let high0:Core.Core_arch.Arm_shared.Neon.t_int32x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vadd_s32 high0 high_tmp
  in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vcombine_s32 low0 low1 } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vcombine_s32 high0 high1 } <: t_SIMD128Vector
  in
  v

let ntt_layer_2_step (v: t_SIMD128Vector) (zeta: i32) =
  let tmp:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_n_s32 v.f_high zeta
  in
  let tmp:Core.Core_arch.Arm_shared.Neon.t_int32x4_t = montgomery_reduce_i32x4_t tmp in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 v.f_low tmp } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s32 v.f_low tmp } <: t_SIMD128Vector
  in
  v

let ntt_multiply (lhs rhs: t_SIMD128Vector) (zeta0 zeta1: i32) =
  let a0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vtrn1q_s32 lhs.f_low lhs.f_high
  in
  let a1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vtrn2q_s32 lhs.f_low lhs.f_high
  in
  let b0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vtrn1q_s32 rhs.f_low rhs.f_high
  in
  let b1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vtrn2q_s32 rhs.f_low rhs.f_high
  in
  let (zetas: t_Array i32 (sz 4)):t_Array i32 (sz 4) =
    let list = [zeta0; zeta1; Core.Ops.Arith.Neg.neg zeta0; Core.Ops.Arith.Neg.neg zeta1] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  let zeta:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_s32 (Rust_primitives.unsize zetas <: t_Slice i32)
  in
  let a0b0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_s32 a0 b0
  in
  let a1b1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_s32 a1 b1
  in
  let a1b1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t = montgomery_reduce_i32x4_t a1b1 in
  let a1b1_zeta:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_s32 a1b1 zeta
  in
  let fst:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s32 a0b0 a1b1_zeta
  in
  let fst:Core.Core_arch.Arm_shared.Neon.t_int32x4_t = montgomery_reduce_i32x4_t fst in
  let a0b1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_s32 a0 b1
  in
  let a1b0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmulq_s32 a1 b0
  in
  let snd:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vaddq_s32 a0b1 a1b0
  in
  let snd:Core.Core_arch.Arm_shared.Neon.t_int32x4_t = montgomery_reduce_i32x4_t snd in
  {
    f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vtrn1q_s32 fst snd;
    f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vtrn2q_s32 fst snd
  }
  <:
  t_SIMD128Vector

let serialize_1_ (v: t_SIMD128Vector) =
  let (shifter0: t_Array i32 (sz 4)):t_Array i32 (sz 4) =
    let list = [0l; 1l; 2l; 3l] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  let (shifter1: t_Array i32 (sz 4)):t_Array i32 (sz 4) =
    let list = [4l; 5l; 6l; 7l] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  let shift0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_s32 (Rust_primitives.unsize shifter0 <: t_Slice i32)
  in
  let shift1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_s32 (Rust_primitives.unsize shifter1 <: t_Slice i32)
  in
  let low:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshlq_s32 v.f_low shift0
  in
  let high:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshlq_s32 v.f_high shift1
  in
  let low:i32 = Libcrux_ml_kem.Simd.Simd128.Neon.vaddvq_s32 low in
  let high:i32 = Libcrux_ml_kem.Simd.Simd128.Neon.vaddvq_s32 high in
  cast (low |. high <: i32) <: u8

let serialize_10_ (v: t_SIMD128Vector) =
  let lowt:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vtrn1q_s32 v.f_low v.f_high
  in
  let hight:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vtrn2q_s32 v.f_low v.f_high
  in
  let mixt:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsliq_n_s32 10l lowt hight
  in
  let lowt:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmovl_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vget_low_s32 mixt
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
  in
  let hight:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmovl_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vget_high_s32 mixt
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
  in
  let mixt:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsliq_n_s64 20l lowt hight
  in
  let (index_arr: t_Array u8 (sz 16)):t_Array u8 (sz 16) =
    let list =
      [0uy; 1uy; 2uy; 3uy; 4uy; 8uy; 9uy; 10uy; 11uy; 12uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  in
  let index:Core.Core_arch.Arm_shared.Neon.t_uint8x16_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_u8 (Rust_primitives.unsize index_arr <: t_Slice u8)
  in
  let mixt:Core.Core_arch.Arm_shared.Neon.t_uint8x16_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vqtbl1q_u8 (Libcrux_ml_kem.Simd.Simd128.Neon.vreinterpretq_u8_s64
          mixt
        <:
        Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
      index
  in
  let result16:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let result16:t_Array u8 (sz 16) = Libcrux_ml_kem.Simd.Simd128.Neon.vst1q_u8 result16 mixt in
  let result10:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
  let result10:t_Array u8 (sz 10) =
    Core.Slice.impl__copy_from_slice result10
      (result16.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 10 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  result10

let serialize_12_ (v: t_SIMD128Vector) =
  let lowt:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vtrn1q_s32 v.f_low v.f_high
  in
  let hight:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vtrn2q_s32 v.f_low v.f_high
  in
  let mixt:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsliq_n_s32 12l lowt hight
  in
  let (index_arr: t_Array u8 (sz 16)):t_Array u8 (sz 16) =
    let list =
      [0uy; 1uy; 2uy; 8uy; 9uy; 10uy; 4uy; 5uy; 6uy; 12uy; 13uy; 14uy; 12uy; 13uy; 14uy; 15uy]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  in
  let index:Core.Core_arch.Arm_shared.Neon.t_uint8x16_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_u8 (Rust_primitives.unsize index_arr <: t_Slice u8)
  in
  let mixt:Core.Core_arch.Arm_shared.Neon.t_uint8x16_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vqtbl1q_u8 (Libcrux_ml_kem.Simd.Simd128.Neon.vreinterpretq_u8_s32
          mixt
        <:
        Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
      index
  in
  let result16:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let result16:t_Array u8 (sz 16) = Libcrux_ml_kem.Simd.Simd128.Neon.vst1q_u8 result16 mixt in
  let result12:t_Array u8 (sz 12) = Rust_primitives.Hax.repeat 0uy (sz 12) in
  let result12:t_Array u8 (sz 12) =
    Core.Slice.impl__copy_from_slice result12
      (result16.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 12 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  result12

let serialize_4_ (v: t_SIMD128Vector) =
  let (shifter0: t_Array i32 (sz 4)):t_Array i32 (sz 4) =
    let list = [0l; 4l; 8l; 12l] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  let (shifter1: t_Array i32 (sz 4)):t_Array i32 (sz 4) =
    let list = [16l; 20l; 24l; 28l] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  let shift0:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_s32 (Rust_primitives.unsize shifter0 <: t_Slice i32)
  in
  let shift1:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vld1q_s32 (Rust_primitives.unsize shifter1 <: t_Slice i32)
  in
  let lowt:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshlq_s32 v.f_low shift0
  in
  let hight:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vshlq_s32 v.f_high shift1
  in
  let low:i32 = Libcrux_ml_kem.Simd.Simd128.Neon.vaddvq_s32 lowt in
  let high:i32 = Libcrux_ml_kem.Simd.Simd128.Neon.vaddvq_s32 hight in
  Core.Num.impl__i32__to_le_bytes (low |. high <: i32)

let serialize_5_ (v: t_SIMD128Vector) =
  let lowt:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vtrn1q_s32 v.f_low v.f_high
  in
  let hight:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vtrn2q_s32 v.f_low v.f_high
  in
  let mixt:Core.Core_arch.Arm_shared.Neon.t_int32x4_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsliq_n_s32 5l lowt hight
  in
  let lowt:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmovl_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vget_low_s32 mixt
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
  in
  let hight:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vmovl_s32 (Libcrux_ml_kem.Simd.Simd128.Neon.vget_high_s32 mixt
        <:
        Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
  in
  let mixt:Core.Core_arch.Arm_shared.Neon.t_int64x2_t =
    Libcrux_ml_kem.Simd.Simd128.Neon.vsliq_n_s64 10l lowt hight
  in
  let result2:t_Array i64 (sz 2) = Rust_primitives.Hax.repeat 0L (sz 2) in
  let result2:t_Array i64 (sz 2) = Libcrux_ml_kem.Simd.Simd128.Neon.vst1q_s64 result2 mixt in
  let result_i64:i64 = (result2.[ sz 0 ] <: i64) |. ((result2.[ sz 1 ] <: i64) <<! 20l <: i64) in
  let result:t_Array u8 (sz 5) = Rust_primitives.Hax.repeat 0uy (sz 5) in
  let result:t_Array u8 (sz 5) =
    Core.Slice.impl__copy_from_slice result
      ((Core.Num.impl__i64__to_le_bytes result_i64 <: t_Array u8 (sz 8)).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 5
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  result

let shift_left (v_SHIFT_BY: i32) (lhs: t_SIMD128Vector) =
  let lhs:t_SIMD128Vector =
    { lhs with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vshlq_n_s32 v_SHIFT_BY lhs.f_low }
    <:
    t_SIMD128Vector
  in
  let lhs:t_SIMD128Vector =
    { lhs with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vshlq_n_s32 v_SHIFT_BY lhs.f_high }
    <:
    t_SIMD128Vector
  in
  lhs

let shift_right (v_SHIFT_BY: i32) (v: t_SIMD128Vector) =
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 v_SHIFT_BY v.f_low }
    <:
    t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vshrq_n_s32 v_SHIFT_BY v.f_high }
    <:
    t_SIMD128Vector
  in
  v

let sub_vec (lhs rhs: t_SIMD128Vector) =
  {
    f_low = Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 lhs.f_low rhs.f_low;
    f_high = Libcrux_ml_kem.Simd.Simd128.Neon.vsubq_s32 lhs.f_high rhs.f_high
  }
  <:
  t_SIMD128Vector

let to_i32_array (v: t_SIMD128Vector) =
  let out:t_Array i32 (sz 8) = Rust_primitives.Hax.repeat 0l (sz 8) in
  let out:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to out
      ({ Core.Ops.Range.f_end = sz 4 } <: Core.Ops.Range.t_RangeTo usize)
      (Libcrux_ml_kem.Simd.Simd128.Neon.vst1q_s32 (out.[ { Core.Ops.Range.f_end = sz 4 }
              <:
              Core.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice i32)
          v.f_low
        <:
        t_Slice i32)
  in
  let out:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core.Ops.Range.f_start = sz 4 } <: Core.Ops.Range.t_RangeFrom usize)
      (Libcrux_ml_kem.Simd.Simd128.Neon.vst1q_s32 (out.[ { Core.Ops.Range.f_start = sz 4 }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice i32)
          v.f_high
        <:
        t_Slice i32)
  in
  out

let deserialize_10_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_10_ v
  in
  Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output

      <:
      t_Array i32 (sz 8))

let deserialize_11_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_11_ v
  in
  Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output

      <:
      t_Array i32 (sz 8))

let deserialize_12_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_12_ v
  in
  Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output

      <:
      t_Array i32 (sz 8))

let deserialize_4_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_4_ v
  in
  Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output

      <:
      t_Array i32 (sz 8))

let deserialize_5_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_5_ v
  in
  Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output

      <:
      t_Array i32 (sz 8))

let serialize_11_ (v: t_SIMD128Vector) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array v
        <:
        t_Array i32 (sz 8))
  in
  Libcrux_ml_kem.Simd.Simd_trait.f_serialize_11_ input
