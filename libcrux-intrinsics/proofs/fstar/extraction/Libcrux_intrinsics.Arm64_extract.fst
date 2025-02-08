module Libcrux_intrinsics.Arm64_extract
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

assume
val e_vdupq_n_s16': i: i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vdupq_n_s16 = e_vdupq_n_s16'

assume
val e_vdupq_n_u64': i: u64 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vdupq_n_u64 = e_vdupq_n_u64'

assume
val e_vst1q_s16': out: t_Slice i16 -> v: u8
  -> Prims.Pure (t_Slice i16) Prims.l_True (fun _ -> Prims.l_True)

let e_vst1q_s16 = e_vst1q_s16'

assume
val e_vst1q_bytes': out: t_Slice u8 -> v: u8
  -> Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let e_vst1q_bytes = e_vst1q_bytes'

assume
val e_vld1q_bytes': bytes: t_Slice u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vld1q_bytes = e_vld1q_bytes'

assume
val e_vld1q_s16': array: t_Slice i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vld1q_s16 = e_vld1q_s16'

assume
val e_vld1q_bytes_u64': array: t_Slice u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vld1q_bytes_u64 = e_vld1q_bytes_u64'

assume
val e_vld1q_u64': array: t_Slice u64 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vld1q_u64 = e_vld1q_u64'

assume
val e_vst1q_u64': out: t_Slice u64 -> v: u8
  -> Prims.Pure (t_Slice u64) Prims.l_True (fun _ -> Prims.l_True)

let e_vst1q_u64 = e_vst1q_u64'

assume
val e_vst1q_bytes_u64': out: t_Slice u8 -> v: u8
  -> Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let e_vst1q_bytes_u64 = e_vst1q_bytes_u64'

assume
val e_vaddq_s16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vaddq_s16 = e_vaddq_s16'

assume
val e_vsubq_s16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vsubq_s16 = e_vsubq_s16'

assume
val e_vmulq_n_s16': v: u8 -> c: i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vmulq_n_s16 = e_vmulq_n_s16'

assume
val e_vmulq_n_u16': v: u8 -> c: u16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vmulq_n_u16 = e_vmulq_n_u16'

assume
val e_vshrq_n_s16': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vshrq_n_s16 (v_SHIFT_BY: i32) = e_vshrq_n_s16' v_SHIFT_BY

assume
val e_vshrq_n_u16': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vshrq_n_u16 (v_SHIFT_BY: i32) = e_vshrq_n_u16' v_SHIFT_BY

assume
val e_vshrq_n_u64': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vshrq_n_u64 (v_SHIFT_BY: i32) = e_vshrq_n_u64' v_SHIFT_BY

assume
val e_vshlq_n_u64': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vshlq_n_u64 (v_SHIFT_BY: i32) = e_vshlq_n_u64' v_SHIFT_BY

assume
val e_vshlq_n_s16': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vshlq_n_s16 (v_SHIFT_BY: i32) = e_vshlq_n_s16' v_SHIFT_BY

assume
val e_vshlq_n_u32': v_SHIFT_BY: i32 -> v: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vshlq_n_u32 (v_SHIFT_BY: i32) = e_vshlq_n_u32' v_SHIFT_BY

assume
val e_vqdmulhq_n_s16': k: u8 -> b: i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vqdmulhq_n_s16 = e_vqdmulhq_n_s16'

assume
val e_vqdmulhq_s16': v: u8 -> c: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vqdmulhq_s16 = e_vqdmulhq_s16'

assume
val e_vcgeq_s16': v: u8 -> c: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vcgeq_s16 = e_vcgeq_s16'

assume
val e_vandq_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vandq_s16 = e_vandq_s16'

assume
val e_vbicq_u64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vbicq_u64 = e_vbicq_u64'

assume
val e_vreinterpretq_s16_u16': m0: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_s16_u16 = e_vreinterpretq_s16_u16'

assume
val e_vreinterpretq_u16_s16': m0: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_u16_s16 = e_vreinterpretq_u16_s16'

assume
val e_vmulq_s16': v: u8 -> c: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vmulq_s16 = e_vmulq_s16'

assume
val e_veorq_s16': mask: u8 -> shifted: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_veorq_s16 = e_veorq_s16'

assume
val e_veorq_u64': mask: u8 -> shifted: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_veorq_u64 = e_veorq_u64'

assume
val e_vdupq_n_u32': value: u32 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vdupq_n_u32 = e_vdupq_n_u32'

assume
val e_vaddq_u32': compressed: u8 -> half: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vaddq_u32 = e_vaddq_u32'

assume
val e_vreinterpretq_s32_u32': compressed: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_s32_u32 = e_vreinterpretq_s32_u32'

assume
val e_vqdmulhq_n_s32': a: u8 -> b: i32 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vqdmulhq_n_s32 = e_vqdmulhq_n_s32'

assume
val e_vreinterpretq_u32_s32': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_u32_s32 = e_vreinterpretq_u32_s32'

assume
val e_vshrq_n_u32': v_N: i32 -> a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vshrq_n_u32 (v_N: i32) = e_vshrq_n_u32' v_N

assume
val e_vandq_u32': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vandq_u32 = e_vandq_u32'

assume
val e_vreinterpretq_u32_s16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_u32_s16 = e_vreinterpretq_u32_s16'

assume
val e_vreinterpretq_s16_u32': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_s16_u32 = e_vreinterpretq_s16_u32'

assume
val e_vtrn1q_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vtrn1q_s16 = e_vtrn1q_s16'

assume
val e_vtrn2q_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vtrn2q_s16 = e_vtrn2q_s16'

assume
val e_vmulq_n_u32': a: u8 -> b: u32 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vmulq_n_u32 = e_vmulq_n_u32'

assume
val e_vtrn1q_s32': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vtrn1q_s32 = e_vtrn1q_s32'

assume
val e_vreinterpretq_s16_s32': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_s16_s32 = e_vreinterpretq_s16_s32'

assume
val e_vreinterpretq_s32_s16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_s32_s16 = e_vreinterpretq_s32_s16'

assume
val e_vtrn2q_s32': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vtrn2q_s32 = e_vtrn2q_s32'

assume
val e_vtrn1q_s64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vtrn1q_s64 = e_vtrn1q_s64'

assume
val e_vtrn1q_u64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vtrn1q_u64 = e_vtrn1q_u64'

assume
val e_vreinterpretq_s16_s64': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_s16_s64 = e_vreinterpretq_s16_s64'

assume
val e_vreinterpretq_s64_s16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_s64_s16 = e_vreinterpretq_s64_s16'

assume
val e_vtrn2q_s64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vtrn2q_s64 = e_vtrn2q_s64'

assume
val e_vtrn2q_u64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vtrn2q_u64 = e_vtrn2q_u64'

assume
val e_vmull_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vmull_s16 = e_vmull_s16'

assume
val e_vget_low_s16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vget_low_s16 = e_vget_low_s16'

assume
val e_vmull_high_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vmull_high_s16 = e_vmull_high_s16'

assume
val e_vmlal_s16': a: u8 -> b: u8 -> c: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vmlal_s16 = e_vmlal_s16'

assume
val e_vmlal_high_s16': a: u8 -> b: u8 -> c: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vmlal_high_s16 = e_vmlal_high_s16'

assume
val e_vld1q_u8': ptr: t_Slice u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vld1q_u8 = e_vld1q_u8'

assume
val e_vreinterpretq_u8_s16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_u8_s16 = e_vreinterpretq_u8_s16'

assume
val e_vqtbl1q_u8': t: u8 -> idx: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vqtbl1q_u8 = e_vqtbl1q_u8'

assume
val e_vreinterpretq_s16_u8': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_s16_u8 = e_vreinterpretq_s16_u8'

assume
val e_vshlq_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vshlq_s16 = e_vshlq_s16'

assume
val e_vshlq_u16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vshlq_u16 = e_vshlq_u16'

assume
val e_vaddv_u16': a: u8 -> Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

let e_vaddv_u16 = e_vaddv_u16'

assume
val e_vget_low_u16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vget_low_u16 = e_vget_low_u16'

assume
val e_vget_high_u16': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vget_high_u16 = e_vget_high_u16'

assume
val e_vaddvq_s16': a: u8 -> Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

let e_vaddvq_s16 = e_vaddvq_s16'

assume
val e_vsliq_n_s32': v_N: i32 -> a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vsliq_n_s32 (v_N: i32) = e_vsliq_n_s32' v_N

assume
val e_vreinterpretq_s64_s32': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_s64_s32 = e_vreinterpretq_s64_s32'

assume
val e_vsliq_n_s64': v_N: i32 -> a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vsliq_n_s64 (v_N: i32) = e_vsliq_n_s64' v_N

assume
val e_vreinterpretq_u8_s64': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_u8_s64 = e_vreinterpretq_u8_s64'

assume
val e_vst1q_u8': out: t_Slice u8 -> v: u8
  -> Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let e_vst1q_u8 = e_vst1q_u8'

assume
val e_vdupq_n_u16': value: u16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vdupq_n_u16 = e_vdupq_n_u16'

assume
val e_vandq_u16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vandq_u16 = e_vandq_u16'

assume
val e_vreinterpretq_u16_u8': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vreinterpretq_u16_u8 = e_vreinterpretq_u16_u8'

assume
val e_vld1q_u16': ptr: t_Slice u16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vld1q_u16 = e_vld1q_u16'

assume
val e_vcleq_s16': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let e_vcleq_s16 = e_vcleq_s16'

assume
val e_vaddvq_u16': a: u8 -> Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

let e_vaddvq_u16 = e_vaddvq_u16'
