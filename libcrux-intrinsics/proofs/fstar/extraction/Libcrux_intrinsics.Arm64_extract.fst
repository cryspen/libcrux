module Libcrux_intrinsics.Arm64_extract
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

assume
val v__vdupq_n_s16': i: i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vdupq_n_s16 = v__vdupq_n_s16'

assume
val v__vdupq_n_u64': i: u64 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vdupq_n_u64 = v__vdupq_n_u64'

assume
val v__vst1q_s16': out: t_Slice i16 -> v: u8
  -> Prims.Pure (t_Slice i16) Prims.l_True (fun _ -> Prims.l_True)

let v__vst1q_s16 = v__vst1q_s16'

assume
val v__vld1q_s16': array: t_Slice i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vld1q_s16 = v__vld1q_s16'

assume
val v__vld1q_bytes_u64': array: t_Slice u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vld1q_bytes_u64 = v__vld1q_bytes_u64'

assume
val v__vld1q_u64': array: t_Slice u64 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vld1q_u64 = v__vld1q_u64'

assume
val v__vst1q_u64': out: t_Slice u64 -> v: u8
  -> Prims.Pure (t_Slice u64) Prims.l_True (fun _ -> Prims.l_True)

let v__vst1q_u64 = v__vst1q_u64'

assume
val v__vst1q_bytes_u64': out: t_Slice u8 -> v: u8
  -> Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let v__vst1q_bytes_u64 = v__vst1q_bytes_u64'

assume
val v__vaddq_s16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vaddq_s16 = v__vaddq_s16'

assume
val v__vsubq_s16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vsubq_s16 = v__vsubq_s16'

assume
val v__vmulq_n_s16': v: u8 -> c: i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vmulq_n_s16 = v__vmulq_n_s16'

assume
val v__vmulq_n_u16': v: u8 -> c: u16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vmulq_n_u16 = v__vmulq_n_u16'

assume
val v__vshrq_n_s16': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vshrq_n_s16 (v_SHIFT_BY: i32) = v__vshrq_n_s16' v_SHIFT_BY

assume
val v__vshrq_n_u16': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vshrq_n_u16 (v_SHIFT_BY: i32) = v__vshrq_n_u16' v_SHIFT_BY

assume
val v__vshrq_n_u64': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vshrq_n_u64 (v_SHIFT_BY: i32) = v__vshrq_n_u64' v_SHIFT_BY

assume
val v__vshlq_n_u64': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vshlq_n_u64 (v_SHIFT_BY: i32) = v__vshlq_n_u64' v_SHIFT_BY

assume
val v__vshlq_n_s16': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vshlq_n_s16 (v_SHIFT_BY: i32) = v__vshlq_n_s16' v_SHIFT_BY

assume
val v__vshlq_n_u32': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vshlq_n_u32 (v_SHIFT_BY: i32) = v__vshlq_n_u32' v_SHIFT_BY

assume
val v__vqdmulhq_n_s16': k: u8 -> b: i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vqdmulhq_n_s16 = v__vqdmulhq_n_s16'

assume
val v__vqdmulhq_s16': v: u8 -> c: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vqdmulhq_s16 = v__vqdmulhq_s16'

assume
val v__vcgeq_s16': v: u8 -> c: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vcgeq_s16 = v__vcgeq_s16'

assume
val v__vandq_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vandq_s16 = v__vandq_s16'

assume
val v__vbicq_u64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vbicq_u64 = v__vbicq_u64'

assume
val v__vreinterpretq_s16_u16': m0: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_s16_u16 = v__vreinterpretq_s16_u16'

assume
val v__vreinterpretq_u16_s16': m0: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_u16_s16 = v__vreinterpretq_u16_s16'

assume
val v__vmulq_s16': v: u8 -> c: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vmulq_s16 = v__vmulq_s16'

assume
val v__veorq_s16': mask: u8 -> shifted: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__veorq_s16 = v__veorq_s16'

assume
val v__veorq_u64': mask: u8 -> shifted: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__veorq_u64 = v__veorq_u64'

assume
val v__vdupq_n_u32': value: u32 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vdupq_n_u32 = v__vdupq_n_u32'

assume
val v__vaddq_u32': compressed: u8 -> half: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vaddq_u32 = v__vaddq_u32'

assume
val v__vreinterpretq_s32_u32': compressed: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_s32_u32 = v__vreinterpretq_s32_u32'

assume
val v__vqdmulhq_n_s32': a: u8 -> b: i32 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vqdmulhq_n_s32 = v__vqdmulhq_n_s32'

assume
val v__vreinterpretq_u32_s32': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_u32_s32 = v__vreinterpretq_u32_s32'

assume
val v__vshrq_n_u32': v_N: i32 -> a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vshrq_n_u32 (v_N: i32) = v__vshrq_n_u32' v_N

assume
val v__vandq_u32': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vandq_u32 = v__vandq_u32'

assume
val v__vreinterpretq_u32_s16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_u32_s16 = v__vreinterpretq_u32_s16'

assume
val v__vreinterpretq_s16_u32': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_s16_u32 = v__vreinterpretq_s16_u32'

assume
val v__vtrn1q_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vtrn1q_s16 = v__vtrn1q_s16'

assume
val v__vtrn2q_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vtrn2q_s16 = v__vtrn2q_s16'

assume
val v__vmulq_n_u32': a: u8 -> b: u32 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vmulq_n_u32 = v__vmulq_n_u32'

assume
val v__vtrn1q_s32': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vtrn1q_s32 = v__vtrn1q_s32'

assume
val v__vreinterpretq_s16_s32': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_s16_s32 = v__vreinterpretq_s16_s32'

assume
val v__vreinterpretq_s32_s16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_s32_s16 = v__vreinterpretq_s32_s16'

assume
val v__vtrn2q_s32': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vtrn2q_s32 = v__vtrn2q_s32'

assume
val v__vtrn1q_s64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vtrn1q_s64 = v__vtrn1q_s64'

assume
val v__vtrn1q_u64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vtrn1q_u64 = v__vtrn1q_u64'

assume
val v__vreinterpretq_s16_s64': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_s16_s64 = v__vreinterpretq_s16_s64'

assume
val v__vreinterpretq_s64_s16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_s64_s16 = v__vreinterpretq_s64_s16'

assume
val v__vtrn2q_s64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vtrn2q_s64 = v__vtrn2q_s64'

assume
val v__vtrn2q_u64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vtrn2q_u64 = v__vtrn2q_u64'

assume
val v__vmull_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vmull_s16 = v__vmull_s16'

assume
val v__vget_low_s16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vget_low_s16 = v__vget_low_s16'

assume
val v__vmull_high_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vmull_high_s16 = v__vmull_high_s16'

assume
val v__vmlal_s16': a: u8 -> b: u8 -> c: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vmlal_s16 = v__vmlal_s16'

assume
val v__vmlal_high_s16': a: u8 -> b: u8 -> c: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vmlal_high_s16 = v__vmlal_high_s16'

assume
val v__vld1q_u8': ptr: t_Slice u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vld1q_u8 = v__vld1q_u8'

assume
val v__vreinterpretq_u8_s16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_u8_s16 = v__vreinterpretq_u8_s16'

assume
val v__vqtbl1q_u8': t: u8 -> idx: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vqtbl1q_u8 = v__vqtbl1q_u8'

assume
val v__vreinterpretq_s16_u8': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_s16_u8 = v__vreinterpretq_s16_u8'

assume
val v__vshlq_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vshlq_s16 = v__vshlq_s16'

assume
val v__vshlq_u16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vshlq_u16 = v__vshlq_u16'

assume
val v__vaddv_u16': a: u8 -> Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

let v__vaddv_u16 = v__vaddv_u16'

assume
val v__vget_low_u16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vget_low_u16 = v__vget_low_u16'

assume
val v__vget_high_u16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vget_high_u16 = v__vget_high_u16'

assume
val v__vaddvq_s16': a: u8 -> Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

let v__vaddvq_s16 = v__vaddvq_s16'

assume
val v__vsliq_n_s32': v_N: i32 -> a: u8 -> b: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vsliq_n_s32 (v_N: i32) = v__vsliq_n_s32' v_N

assume
val v__vreinterpretq_s64_s32': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_s64_s32 = v__vreinterpretq_s64_s32'

assume
val v__vsliq_n_s64': v_N: i32 -> a: u8 -> b: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vsliq_n_s64 (v_N: i32) = v__vsliq_n_s64' v_N

assume
val v__vreinterpretq_u8_s64': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_u8_s64 = v__vreinterpretq_u8_s64'

assume
val v__vst1q_u8': out: t_Slice u8 -> v: u8
  -> Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let v__vst1q_u8 = v__vst1q_u8'

assume
val v__vdupq_n_u16': value: u16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vdupq_n_u16 = v__vdupq_n_u16'

assume
val v__vandq_u16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vandq_u16 = v__vandq_u16'

assume
val v__vreinterpretq_u16_u8': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vreinterpretq_u16_u8 = v__vreinterpretq_u16_u8'

assume
val v__vld1q_u16': ptr: t_Slice u16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vld1q_u16 = v__vld1q_u16'

assume
val v__vcleq_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v__vcleq_s16 = v__vcleq_s16'

assume
val v__vaddvq_u16': a: u8 -> Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

let v__vaddvq_u16 = v__vaddvq_u16'
