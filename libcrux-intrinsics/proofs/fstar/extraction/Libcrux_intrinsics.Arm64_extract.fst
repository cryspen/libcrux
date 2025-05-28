module Libcrux_intrinsics.Arm64_extract
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let e_vdupq_n_s16 (i: i16) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vdupq_n_u64 (i: u64) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vst1q_s16 (out: t_Slice i16) (v: u8) : t_Slice i16 =
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  out

let e_vst1q_bytes (out: t_Slice u8) (v: u8) : t_Slice u8 =
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  out

let e_vld1q_bytes (bytes: t_Slice u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vld1q_s16 (array: t_Slice i16) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vld1q_bytes_u64 (array: t_Slice u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vld1q_u64 (array: t_Slice u64) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vst1q_u64 (out: t_Slice u64) (v: u8) : t_Slice u64 =
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  out

let e_vst1q_bytes_u64 (out: t_Slice u8) (v: u8) : t_Slice u8 =
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  out

let e_vaddq_s16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vsubq_s16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vmulq_n_s16 (v: u8) (c: i16) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vmulq_n_u16 (v: u8) (c: u16) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vshrq_n_s16 (v_SHIFT_BY: i32) (v: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vshrq_n_u16 (v_SHIFT_BY: i32) (v: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vshrq_n_u64 (v_SHIFT_BY: i32) (v: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vxarq_u64 (v_LEFT v_RIGHT: i32) (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vshlq_n_u64 (v_SHIFT_BY: i32) (v: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vshlq_n_s16 (v_SHIFT_BY: i32) (v: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vshlq_n_u32 (v_SHIFT_BY: i32) (v: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vqdmulhq_n_s16 (k: u8) (b: i16) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vqdmulhq_s16 (v c: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vcgeq_s16 (v c: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vandq_s16 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vbicq_u64 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vbcaxq_u64 (a b c: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_s16_u16 (m0: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_u16_s16 (m0: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vmulq_s16 (v c: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_veorq_s16 (mask shifted: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_veorq_u64 (mask shifted: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vrax1q_u64 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_veor3q_u64 (a b c: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vdupq_n_u32 (value: u32) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vaddq_u32 (compressed half: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_s32_u32 (compressed: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vqdmulhq_n_s32 (a: u8) (b: i32) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_u32_s32 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vshrq_n_u32 (v_N: i32) (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vandq_u32 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_u32_s16 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_s16_u32 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vtrn1q_s16 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vtrn2q_s16 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vmulq_n_u32 (a: u8) (b: u32) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vtrn1q_s32 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_s16_s32 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_s32_s16 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vtrn2q_s32 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vtrn1q_s64 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vtrn1q_u64 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_s16_s64 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_s64_s16 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vtrn2q_s64 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vtrn2q_u64 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vmull_s16 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vget_low_s16 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vmull_high_s16 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vmlal_s16 (a b c: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vmlal_high_s16 (a b c: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vld1q_u8 (ptr: t_Slice u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_u8_s16 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vqtbl1q_u8 (t idx: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_s16_u8 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vshlq_s16 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vshlq_u16 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vaddv_u16 (a: u8) : u16 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vget_low_u16 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vget_high_u16 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vaddvq_s16 (a: u8) : i16 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vsliq_n_s32 (v_N: i32) (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_s64_s32 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vsliq_n_s64 (v_N: i32) (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_u8_s64 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vst1q_u8 (out: t_Slice u8) (v: u8) : t_Slice u8 =
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  out

let e_vdupq_n_u16 (value: u16) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vandq_u16 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vreinterpretq_u16_u8 (a: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vld1q_u16 (ptr: t_Slice u16) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vcleq_s16 (a b: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let e_vaddvq_u16 (a: u8) : u16 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)
