module Libcrux_polynomials_aarch64.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val v__vaddq_s16 (lhs rhs: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vaddq_u32 (compressed half: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vaddv_u16 (a: Core.Core_arch.Arm_shared.Neon.t_uint16x4_t)
    : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val v__vaddvq_s16 (a: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val v__vaddvq_u16 (a: Core.Core_arch.Arm_shared.Neon.t_uint16x8_t)
    : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val v__vandq_s16 (a b: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vandq_u16 (a b: Core.Core_arch.Arm_shared.Neon.t_uint16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vandq_u32 (a b: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vcgeq_s16 (v c: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vcleq_s16 (a b: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vdupq_n_s16 (i: i16)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vdupq_n_u16 (value: u16)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vdupq_n_u32 (value: u32)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__veorq_s16 (mask shifted: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vget_high_u16 (a: Core.Core_arch.Arm_shared.Neon.t_uint16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vget_low_s16 (a: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vget_low_u16 (a: Core.Core_arch.Arm_shared.Neon.t_uint16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vld1q_s16 (array: t_Slice i16)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vld1q_u16 (ptr: t_Slice u16)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vld1q_u8 (ptr: t_Slice u8)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint8x16_t Prims.l_True (fun _ -> Prims.l_True)

val v__vmlal_high_s16
      (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
      (b c: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vmlal_s16
      (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
      (b c: Core.Core_arch.Arm_shared.Neon.t_int16x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vmull_high_s16 (a b: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vmull_s16 (a b: Core.Core_arch.Arm_shared.Neon.t_int16x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vmulq_n_s16 (v: Core.Core_arch.Arm_shared.Neon.t_int16x8_t) (c: i16)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vmulq_n_u16 (v: Core.Core_arch.Arm_shared.Neon.t_uint16x8_t) (c: u16)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vmulq_n_u32 (a: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t) (b: u32)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vmulq_s16 (v c: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vqdmulhq_n_s16 (k: Core.Core_arch.Arm_shared.Neon.t_int16x8_t) (b: i16)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vqdmulhq_n_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t) (b: i32)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vqdmulhq_s16 (v c: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vqtbl1q_u8 (t idx: Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint8x16_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_s16_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_s16_s64 (a: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_s16_u16 (m0: Core.Core_arch.Arm_shared.Neon.t_uint16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_s16_u32 (a: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_s16_u8 (a: Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_s32_s16 (a: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_s32_u32 (compressed: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_s64_s16 (a: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_s64_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_u16_s16 (m0: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_u16_u8 (a: Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_u32_s16 (a: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_u32_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_u8_s16 (a: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint8x16_t Prims.l_True (fun _ -> Prims.l_True)

val v__vreinterpretq_u8_s64 (a: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint8x16_t Prims.l_True (fun _ -> Prims.l_True)

val v__vshlq_n_s16 (v_SHIFT_BY: i32) (v: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vshlq_n_u32 (v_SHIFT_BY: i32) (v: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vshlq_s16 (a b: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vshlq_u16
      (a: Core.Core_arch.Arm_shared.Neon.t_uint16x8_t)
      (b: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vshrq_n_s16 (v_SHIFT_BY: i32) (v: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vshrq_n_u16 (v_SHIFT_BY: i32) (v: Core.Core_arch.Arm_shared.Neon.t_uint16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vshrq_n_u32 (v_N: i32) (a: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vsliq_n_s32 (v_N: i32) (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vsliq_n_s64 (v_N: i32) (a b: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val v__vst1q_s16 (out: t_Slice i16) (v: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure (t_Slice i16) Prims.l_True (fun _ -> Prims.l_True)

val v__vst1q_u8 (out: t_Slice u8) (v: Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val v__vsubq_s16 (lhs rhs: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vtrn1q_s16 (a b: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vtrn1q_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vtrn1q_s64 (a b: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val v__vtrn2q_s16 (a b: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val v__vtrn2q_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val v__vtrn2q_s64 (a b: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)
