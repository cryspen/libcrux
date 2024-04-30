module Libcrux_ml_kem.Simd.Simd128.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_int16x4_t = Core.Core_arch.Arm_shared.Neon.t_int16x4_t

unfold
let t_int32x2_t = Core.Core_arch.Arm_shared.Neon.t_int32x2_t

unfold
let t_int32x4_t = Core.Core_arch.Arm_shared.Neon.t_int32x4_t

unfold
let t_int64x2_t = Core.Core_arch.Arm_shared.Neon.t_int64x2_t

unfold
let t_uint32x4_t = Core.Core_arch.Arm_shared.Neon.t_uint32x4_t

unfold
let t_uint8x16_t = Core.Core_arch.Arm_shared.Neon.t_uint8x16_t

val vadd_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x2_t Prims.l_True (fun _ -> Prims.l_True)

val vaddq_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vaddq_s64 (a b: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val vaddvq_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val vand_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x2_t Prims.l_True (fun _ -> Prims.l_True)

val vandq_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vcgeq_s32_reinterpreted (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vcombine_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vdup_n_s32 (v: i32)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x2_t Prims.l_True (fun _ -> Prims.l_True)

val vdupq_n_s32 (v: i32)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vdupq_n_s64 (v: i64)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val veorq_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vget_high_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x2_t Prims.l_True (fun _ -> Prims.l_True)

val vget_low_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x2_t Prims.l_True (fun _ -> Prims.l_True)

val vld1q_s32 (v: t_Slice i32)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vld1q_u8 (v: t_Slice u8)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint8x16_t Prims.l_True (fun _ -> Prims.l_True)

val vmovl_s16 (a: Core.Core_arch.Arm_shared.Neon.t_int16x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vmovl_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val vmovn_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x4_t Prims.l_True (fun _ -> Prims.l_True)

val vmovn_s64 (a: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x2_t Prims.l_True (fun _ -> Prims.l_True)

val vmul_n_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x2_t) (b: i32)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x2_t Prims.l_True (fun _ -> Prims.l_True)

val vmull_high_n_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t) (b: i32)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val vmull_n_s16 (a: Core.Core_arch.Arm_shared.Neon.t_int16x4_t) (b: i16)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vmull_n_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x2_t) (b: i32)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val vmulq_n_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t) (b: i32)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vmulq_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vqtbl1q_u8 (t idx: Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint8x16_t Prims.l_True (fun _ -> Prims.l_True)

val vreinterpret_s16_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x4_t Prims.l_True (fun _ -> Prims.l_True)

val vreinterpretq_s32_u32 (a: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vreinterpretq_s64_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val vreinterpretq_u32_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vreinterpretq_u8_s32 (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint8x16_t Prims.l_True (fun _ -> Prims.l_True)

val vreinterpretq_u8_s64 (a: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint8x16_t Prims.l_True (fun _ -> Prims.l_True)

val vshlq_n_s32 (v_N: i32) (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vshlq_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vshr_n_s32 (v_N: i32) (a: Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x2_t Prims.l_True (fun _ -> Prims.l_True)

val vshrq_n_s32 (v_N: i32) (a: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vshrq_n_s64 (v_N: i32) (a: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val vshrq_n_u32 (v_N: i32) (a: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vsliq_n_s32 (v_N: i32) (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vsliq_n_s64 (v_N: i32) (a b: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int64x2_t Prims.l_True (fun _ -> Prims.l_True)

val vst1q_s32 (out: t_Slice i32) (v: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure (t_Slice i32) Prims.l_True (fun _ -> Prims.l_True)

val vst1q_s64 (out: t_Slice i64) (v: Core.Core_arch.Arm_shared.Neon.t_int64x2_t)
    : Prims.Pure (t_Slice i64) Prims.l_True (fun _ -> Prims.l_True)

val vst1q_u8 (out: t_Slice u8) (v: Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val vsub_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x2_t Prims.l_True (fun _ -> Prims.l_True)

val vsubq_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vtrn1q_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)

val vtrn2q_s32 (a b: Core.Core_arch.Arm_shared.Neon.t_int32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int32x4_t Prims.l_True (fun _ -> Prims.l_True)
