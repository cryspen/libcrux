module Libcrux_polynomials_aarch64.Rejsample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let rej_sample (a: t_Slice u8) =
  let (neon_bits: t_Array u16 (sz 8)):t_Array u16 (sz 8) =
    let list = [1us; 2us; 4us; 8us; 16us; 32us; 64us; 128us] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let bits:Core.Core_arch.Arm_shared.Neon.t_uint16x8_t =
    Libcrux_polynomials_aarch64.Neon.v__vld1q_u16 (Rust_primitives.unsize neon_bits <: t_Slice u16)
  in
  let fm:Core.Core_arch.Arm_shared.Neon.t_int16x8_t =
    Libcrux_polynomials_aarch64.Neon.v__vdupq_n_s16 3328s
  in
  let input:Libcrux_polynomials_aarch64.Simd128ops.t_SIMD128Vector =
    Libcrux_polynomials_aarch64.Simd128ops.deserialize_12_ a
  in
  let mask0:Core.Core_arch.Arm_shared.Neon.t_uint16x8_t =
    Libcrux_polynomials_aarch64.Neon.v__vcleq_s16 input.Libcrux_polynomials_aarch64.Simd128ops.f_low
      fm
  in
  let mask1:Core.Core_arch.Arm_shared.Neon.t_uint16x8_t =
    Libcrux_polynomials_aarch64.Neon.v__vcleq_s16 input
        .Libcrux_polynomials_aarch64.Simd128ops.f_high
      fm
  in
  let used0:u16 =
    Libcrux_polynomials_aarch64.Neon.v__vaddvq_u16 (Libcrux_polynomials_aarch64.Neon.v__vandq_u16 mask0
          bits
        <:
        Core.Core_arch.Arm_shared.Neon.t_uint16x8_t)
  in
  let used1:u16 =
    Libcrux_polynomials_aarch64.Neon.v__vaddvq_u16 (Libcrux_polynomials_aarch64.Neon.v__vandq_u16 mask1
          bits
        <:
        Core.Core_arch.Arm_shared.Neon.t_uint16x8_t)
  in
  let pick0:u32 = Core.Num.impl__u16__count_ones used0 in
  let pick1:u32 = Core.Num.impl__u16__count_ones used1 in
  let index_vec0:Core.Core_arch.Arm_shared.Neon.t_uint8x16_t =
    Libcrux_polynomials_aarch64.Neon.v__vld1q_u8 (Rust_primitives.unsize (v_IDX_TABLE.[ cast (used0
                  <:
                  u16)
              <:
              usize ]
            <:
            t_Array u8 (sz 16))
        <:
        t_Slice u8)
  in
  let shifted0:Core.Core_arch.Arm_shared.Neon.t_int16x8_t =
    Libcrux_polynomials_aarch64.Neon.v__vreinterpretq_s16_u8 (Libcrux_polynomials_aarch64.Neon.v__vqtbl1q_u8
          (Libcrux_polynomials_aarch64.Neon.v__vreinterpretq_u8_s16 input
                .Libcrux_polynomials_aarch64.Simd128ops.f_low
            <:
            Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
          index_vec0
        <:
        Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
  in
  let index_vec1:Core.Core_arch.Arm_shared.Neon.t_uint8x16_t =
    Libcrux_polynomials_aarch64.Neon.v__vld1q_u8 (Rust_primitives.unsize (v_IDX_TABLE.[ cast (used1
                  <:
                  u16)
              <:
              usize ]
            <:
            t_Array u8 (sz 16))
        <:
        t_Slice u8)
  in
  let shifted1:Core.Core_arch.Arm_shared.Neon.t_int16x8_t =
    Libcrux_polynomials_aarch64.Neon.v__vreinterpretq_s16_u8 (Libcrux_polynomials_aarch64.Neon.v__vqtbl1q_u8
          (Libcrux_polynomials_aarch64.Neon.v__vreinterpretq_u8_s16 input
                .Libcrux_polynomials_aarch64.Simd128ops.f_high
            <:
            Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
          index_vec1
        <:
        Core.Core_arch.Arm_shared.Neon.t_uint8x16_t)
  in
  let (out: t_Array i16 (sz 16)):t_Array i16 (sz 16) = Rust_primitives.Hax.repeat 0s (sz 16) in
  let idx0:usize = cast (pick0 <: u32) <: usize in
  let out:t_Array i16 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_polynomials_aarch64.Neon.v__vst1q_s16 (out.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = sz 8
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
          shifted0
        <:
        t_Slice i16)
  in
  let out:t_Array i16 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({ Core.Ops.Range.f_start = idx0; Core.Ops.Range.f_end = idx0 +! sz 8 <: usize }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_polynomials_aarch64.Neon.v__vst1q_s16 (out.[ {
                Core.Ops.Range.f_start = idx0;
                Core.Ops.Range.f_end = idx0 +! sz 8 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
          shifted1
        <:
        t_Slice i16)
  in
  (cast (pick0 +! pick1 <: u32) <: usize), out <: (usize & t_Array i16 (sz 16))
