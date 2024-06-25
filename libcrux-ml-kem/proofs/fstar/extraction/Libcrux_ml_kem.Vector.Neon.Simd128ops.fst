module Libcrux_ml_kem.Vector.Neon.Simd128ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compress_int32x4_t (v_COEFFICIENT_BITS: i32) (v: u8) =
  let half:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_u32 1664ul in
  let compressed:u8 = Libcrux_intrinsics.Arm64_extract.v__vshlq_n_u32 v_COEFFICIENT_BITS v in
  let compressed:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_u32 compressed half in
  let compressed:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s32 (Libcrux_intrinsics.Arm64_extract.v__vqdmulhq_n_s32
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_u32 compressed <: u8)
          10321340l
        <:
        u8)
  in
  Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 4l compressed

let mask_n_least_significant_bits (coefficient_bits: i16) =
  match coefficient_bits with
  | 4s -> 15s
  | 5s -> 31s
  | 10s -> 1023s
  | 11s -> 2047s
  | x -> (1s <<! x <: i16) -! 1s

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

let decompress_uint32x4_t (v_COEFFICIENT_BITS: i32) (v: u8) =
  let coeff:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vdupq_n_u32 (1ul <<! (v_COEFFICIENT_BITS -! 1l <: i32)
        <:
        u32)
  in
  let decompressed:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vmulq_n_u32 v
      (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: u32)
  in
  let decompressed:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_u32 decompressed coeff in
  Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 v_COEFFICIENT_BITS decompressed

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

let v_ZERO (_: Prims.unit) =
  {
    f_low = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 0s;
    f_high = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 0s
  }
  <:
  t_SIMD128Vector

let add (lhs rhs: t_SIMD128Vector) =
  let lhs:t_SIMD128Vector =
    { lhs with f_low = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 lhs.f_low rhs.f_low }
    <:
    t_SIMD128Vector
  in
  let lhs:t_SIMD128Vector =
    { lhs with f_high = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 lhs.f_high rhs.f_high }
    <:
    t_SIMD128Vector
  in
  lhs

let barrett_reduce (v: t_SIMD128Vector) =
  let v:t_SIMD128Vector = { v with f_low = barrett_reduce_int16x8_t v.f_low } <: t_SIMD128Vector in
  let v:t_SIMD128Vector =
    { v with f_high = barrett_reduce_int16x8_t v.f_high } <: t_SIMD128Vector
  in
  v

let bitwise_and_with_constant (v: t_SIMD128Vector) (c: i16) =
  let c:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 c in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_intrinsics.Arm64_extract.v__vandq_s16 v.f_low c } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_intrinsics.Arm64_extract.v__vandq_s16 v.f_high c } <: t_SIMD128Vector
  in
  v

let compress (v_COEFFICIENT_BITS: i32) (v: t_SIMD128Vector) =
  let mask:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 (mask_n_least_significant_bits (cast (v_COEFFICIENT_BITS
                <:
                i32)
            <:
            i16)
        <:
        i16)
  in
  let mask16:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_u32 65535ul in
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_u32 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16
          v.f_low
        <:
        u8)
      mask16
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 16l
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16 v.f_low <: u8)
  in
  let high0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_u32 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16
          v.f_high
        <:
        u8)
      mask16
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 16l
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16 v.f_high <: u8)
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
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_intrinsics.Arm64_extract.v__vandq_s16 low mask } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_intrinsics.Arm64_extract.v__vandq_s16 high mask } <: t_SIMD128Vector
  in
  v

let compress_1_ (v: t_SIMD128Vector) =
  let half:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 1664s in
  let quarter:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 832s in
  let shifted:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 half v.f_low in
  let mask:u8 = Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 15l shifted in
  let shifted_to_positive:u8 = Libcrux_intrinsics.Arm64_extract.v__veorq_s16 mask shifted in
  let shifted_positive_in_range:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 shifted_to_positive quarter
  in
  let v:t_SIMD128Vector =
    {
      v with
      f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 (Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u16
            15l
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_s16 shifted_positive_in_range
              <:
              u8)
          <:
          u8)
    }
    <:
    t_SIMD128Vector
  in
  let shifted:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 half v.f_high in
  let mask:u8 = Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 15l shifted in
  let shifted_to_positive:u8 = Libcrux_intrinsics.Arm64_extract.v__veorq_s16 mask shifted in
  let shifted_positive_in_range:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 shifted_to_positive quarter
  in
  let v:t_SIMD128Vector =
    {
      v with
      f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 (Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u16
            15l
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_s16 shifted_positive_in_range
              <:
              u8)
          <:
          u8)
    }
    <:
    t_SIMD128Vector
  in
  v

let cond_subtract_3329_ (v: t_SIMD128Vector) =
  let c:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 3329s in
  let m0:u8 = Libcrux_intrinsics.Arm64_extract.v__vcgeq_s16 v.f_low c in
  let m1:u8 = Libcrux_intrinsics.Arm64_extract.v__vcgeq_s16 v.f_high c in
  let c0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_s16 c
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 m0 <: u8)
  in
  let c1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_s16 c
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 m1 <: u8)
  in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 v.f_low c0 } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 v.f_high c1 } <: t_SIMD128Vector
  in
  v

let decompress_ciphertext_coefficient (v_COEFFICIENT_BITS: i32) (v: t_SIMD128Vector) =
  let mask16:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_u32 65535ul in
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_u32 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16
          v.f_low
        <:
        u8)
      mask16
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 16l
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16 v.f_low <: u8)
  in
  let high0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vandq_u32 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16
          v.f_high
        <:
        u8)
      mask16
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshrq_n_u32 16l
      (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u32_s16 v.f_high <: u8)
  in
  let low0:u8 = decompress_uint32x4_t v_COEFFICIENT_BITS low0 in
  let low1:u8 = decompress_uint32x4_t v_COEFFICIENT_BITS low1 in
  let high0:u8 = decompress_uint32x4_t v_COEFFICIENT_BITS high0 in
  let high1:u8 = decompress_uint32x4_t v_COEFFICIENT_BITS high1 in
  let v:t_SIMD128Vector =
    {
      v with
      f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32
            low0
          <:
          u8)
        (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32 low1 <: u8)
    }
    <:
    t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    {
      v with
      f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32
            high0
          <:
          u8)
        (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u32 high1 <: u8)
    }
    <:
    t_SIMD128Vector
  in
  v

let deserialize_1_ (a: t_Slice u8) =
  let one:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 1s in
  let low:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 (cast (a.[ sz 0 ] <: u8) <: i16) in
  let high:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 (cast (a.[ sz 1 ] <: u8) <: i16) in
  let (shifter: t_Array i16 (sz 8)):t_Array i16 (sz 8) =
    let list = [0s; 255s; (-2s); (-3s); (-4s); (-5s); (-6s); (-7s)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let shift:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize shifter <: t_Slice i16)
  in
  let low:u8 = Libcrux_intrinsics.Arm64_extract.v__vshlq_s16 low shift in
  let high:u8 = Libcrux_intrinsics.Arm64_extract.v__vshlq_s16 high shift in
  {
    f_low = Libcrux_intrinsics.Arm64_extract.v__vandq_s16 low one;
    f_high = Libcrux_intrinsics.Arm64_extract.v__vandq_s16 high one
  }
  <:
  t_SIMD128Vector

let deserialize_10_ (v: t_Slice u8) =
  let input0:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let input1:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let input2:t_Array u8 (sz 4) = Rust_primitives.Hax.repeat 0uy (sz 4) in
  let input0:t_Array u8 (sz 8) =
    Core.Slice.impl__copy_from_slice #u8
      input0
      (v.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let input1:t_Array u8 (sz 8) =
    Core.Slice.impl__copy_from_slice #u8
      input1
      (v.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let input2:t_Array u8 (sz 4) =
    Core.Slice.impl__copy_from_slice #u8
      input2
      (v.[ { Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 20 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let input0:u64 = Core.Num.impl__u64__from_le_bytes input0 in
  let input1:u64 = Core.Num.impl__u64__from_le_bytes input1 in
  let input2:u32 = Core.Num.impl__u32__from_le_bytes input2 in
  let low:t_Array i16 (sz 8) = Rust_primitives.Hax.repeat 0s (sz 8) in
  let high:t_Array i16 (sz 8) = Rust_primitives.Hax.repeat 0s (sz 8) in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 0)
      (cast (input0 &. 1023uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 1)
      (cast ((input0 >>! 10l <: u64) &. 1023uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 2)
      (cast ((input0 >>! 20l <: u64) &. 1023uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 3)
      (cast ((input0 >>! 30l <: u64) &. 1023uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 4)
      (cast ((input0 >>! 40l <: u64) &. 1023uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 5)
      (cast ((input0 >>! 50l <: u64) &. 1023uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 6)
      (cast (((input0 >>! 60l <: u64) |. (input1 <<! 4l <: u64) <: u64) &. 1023uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 7)
      (cast ((input1 >>! 6l <: u64) &. 1023uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 0)
      (cast ((input1 >>! 16l <: u64) &. 1023uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 1)
      (cast ((input1 >>! 26l <: u64) &. 1023uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 2)
      (cast ((input1 >>! 36l <: u64) &. 1023uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 3)
      (cast ((input1 >>! 46l <: u64) &. 1023uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 4)
      (cast (((cast (input1 >>! 56l <: u64) <: u32) |. (input2 <<! 8l <: u32) <: u32) &. 1023ul
            <:
            u32)
        <:
        i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 5)
      (cast ((input2 >>! 2l <: u32) &. 1023ul <: u32) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 6)
      (cast ((input2 >>! 12l <: u32) &. 1023ul <: u32) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 7)
      (cast ((input2 >>! 22l <: u32) &. 1023ul <: u32) <: i16)
  in
  {
    f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize low <: t_Slice i16);
    f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize high <: t_Slice i16)
  }
  <:
  t_SIMD128Vector

let deserialize_11_ (v: t_Slice u8) =
  let input0:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let input1:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let input2:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let input0:t_Array u8 (sz 8) =
    Core.Slice.impl__copy_from_slice #u8
      input0
      (v.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let input1:t_Array u8 (sz 8) =
    Core.Slice.impl__copy_from_slice #u8
      input1
      (v.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let input2:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range input2
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 6 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (input2.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 6 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (v.[ { Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 22 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let input0:u64 = Core.Num.impl__u64__from_le_bytes input0 in
  let input1:u64 = Core.Num.impl__u64__from_le_bytes input1 in
  let input2:u64 = Core.Num.impl__u64__from_le_bytes input2 in
  let low:t_Array i16 (sz 8) = Rust_primitives.Hax.repeat 0s (sz 8) in
  let high:t_Array i16 (sz 8) = Rust_primitives.Hax.repeat 0s (sz 8) in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 0)
      (cast (input0 &. 2047uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 1)
      (cast ((input0 >>! 11l <: u64) &. 2047uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 2)
      (cast ((input0 >>! 22l <: u64) &. 2047uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 3)
      (cast ((input0 >>! 33l <: u64) &. 2047uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 4)
      (cast ((input0 >>! 44l <: u64) &. 2047uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 5)
      (cast (((input0 >>! 55l <: u64) |. (input1 <<! 9l <: u64) <: u64) &. 2047uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 6)
      (cast ((input1 >>! 2l <: u64) &. 2047uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 7)
      (cast ((input1 >>! 13l <: u64) &. 2047uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 0)
      (cast ((input1 >>! 24l <: u64) &. 2047uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 1)
      (cast ((input1 >>! 35l <: u64) &. 2047uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 2)
      (cast ((input1 >>! 46l <: u64) &. 2047uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 3)
      (cast (((input1 >>! 57l <: u64) |. (input2 <<! 7l <: u64) <: u64) &. 2047uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 4)
      (cast ((input2 >>! 4l <: u64) &. 2047uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 5)
      (cast ((input2 >>! 15l <: u64) &. 2047uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 6)
      (cast ((input2 >>! 26l <: u64) &. 2047uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 7)
      (cast ((input2 >>! 37l <: u64) &. 2047uL <: u64) <: i16)
  in
  {
    f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize low <: t_Slice i16);
    f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize high <: t_Slice i16)
  }
  <:
  t_SIMD128Vector

let deserialize_12_ (v: t_Slice u8) =
  let (indexes: t_Array u8 (sz 16)):t_Array u8 (sz 16) =
    let list =
      [0uy; 1uy; 1uy; 2uy; 3uy; 4uy; 4uy; 5uy; 6uy; 7uy; 7uy; 8uy; 9uy; 10uy; 10uy; 11uy]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  in
  let index_vec:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_u8 (Rust_primitives.unsize indexes <: t_Slice u8)
  in
  let (shifts: t_Array i16 (sz 8)):t_Array i16 (sz 8) =
    let list = [0s; (-4s); 0s; (-4s); 0s; (-4s); 0s; (-4s)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let shift_vec:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize shifts <: t_Slice i16)
  in
  let mask12:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_u16 4095us in
  let input0:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let input0:t_Array u8 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range input0
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 12 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (input0.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 12 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (v.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 12 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let input_vec0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_u8 (Rust_primitives.unsize input0 <: t_Slice u8)
  in
  let input1:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let input1:t_Array u8 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range input1
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 12 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (input1.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 12 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (v.[ { Core.Ops.Range.f_start = sz 12; Core.Ops.Range.f_end = sz 24 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let input_vec1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_u8 (Rust_primitives.unsize input1 <: t_Slice u8)
  in
  let moved0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_u8 (Libcrux_intrinsics.Arm64_extract.v__vqtbl1q_u8
          input_vec0
          index_vec
        <:
        u8)
  in
  let shifted0:u8 = Libcrux_intrinsics.Arm64_extract.v__vshlq_u16 moved0 shift_vec in
  let low:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 (Libcrux_intrinsics.Arm64_extract.v__vandq_u16
          shifted0
          mask12
        <:
        u8)
  in
  let moved1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_u8 (Libcrux_intrinsics.Arm64_extract.v__vqtbl1q_u8
          input_vec1
          index_vec
        <:
        u8)
  in
  let shifted1:u8 = Libcrux_intrinsics.Arm64_extract.v__vshlq_u16 moved1 shift_vec in
  let high:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u16 (Libcrux_intrinsics.Arm64_extract.v__vandq_u16
          shifted1
          mask12
        <:
        u8)
  in
  { f_low = low; f_high = high } <: t_SIMD128Vector

let deserialize_4_ (v: t_Slice u8) =
  let input:u64 =
    Core.Num.impl__u64__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (sz 8))
          #Core.Array.t_TryFromSliceError
          (Core.Convert.f_try_into #(t_Slice u8) #(t_Array u8 (sz 8)) v
            <:
            Core.Result.t_Result (t_Array u8 (sz 8)) Core.Array.t_TryFromSliceError)
        <:
        t_Array u8 (sz 8))
  in
  let low:t_Array i16 (sz 8) = Rust_primitives.Hax.repeat 0s (sz 8) in
  let high:t_Array i16 (sz 8) = Rust_primitives.Hax.repeat 0s (sz 8) in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 0)
      (cast (input &. 15uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 1)
      (cast ((input >>! 4l <: u64) &. 15uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 2)
      (cast ((input >>! 8l <: u64) &. 15uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 3)
      (cast ((input >>! 12l <: u64) &. 15uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 4)
      (cast ((input >>! 16l <: u64) &. 15uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 5)
      (cast ((input >>! 20l <: u64) &. 15uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 6)
      (cast ((input >>! 24l <: u64) &. 15uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 7)
      (cast ((input >>! 28l <: u64) &. 15uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 0)
      (cast ((input >>! 32l <: u64) &. 15uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 1)
      (cast ((input >>! 36l <: u64) &. 15uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 2)
      (cast ((input >>! 40l <: u64) &. 15uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 3)
      (cast ((input >>! 44l <: u64) &. 15uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 4)
      (cast ((input >>! 48l <: u64) &. 15uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 5)
      (cast ((input >>! 52l <: u64) &. 15uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 6)
      (cast ((input >>! 56l <: u64) &. 15uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 7)
      (cast ((input >>! 60l <: u64) &. 15uL <: u64) <: i16)
  in
  {
    f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize low <: t_Slice i16);
    f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize high <: t_Slice i16)
  }
  <:
  t_SIMD128Vector

let deserialize_5_ (v: t_Slice u8) =
  let input0:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let input0:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range input0
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (input0.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (v.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let low64:u64 = Core.Num.impl__u64__from_le_bytes input0 in
  let input1:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let input1:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range input1
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (input1.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (v.[ { Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 10 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let high64:u64 = Core.Num.impl__u64__from_le_bytes input1 in
  let low:t_Array i16 (sz 8) = Rust_primitives.Hax.repeat 0s (sz 8) in
  let high:t_Array i16 (sz 8) = Rust_primitives.Hax.repeat 0s (sz 8) in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 0)
      (cast (low64 &. 31uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 1)
      (cast ((low64 >>! 5l <: u64) &. 31uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 2)
      (cast ((low64 >>! 10l <: u64) &. 31uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 3)
      (cast ((low64 >>! 15l <: u64) &. 31uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 4)
      (cast ((low64 >>! 20l <: u64) &. 31uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 5)
      (cast ((low64 >>! 25l <: u64) &. 31uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 6)
      (cast ((low64 >>! 30l <: u64) &. 31uL <: u64) <: i16)
  in
  let low:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
      (sz 7)
      (cast ((low64 >>! 35l <: u64) &. 31uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 0)
      (cast (high64 &. 31uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 1)
      (cast ((high64 >>! 5l <: u64) &. 31uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 2)
      (cast ((high64 >>! 10l <: u64) &. 31uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 3)
      (cast ((high64 >>! 15l <: u64) &. 31uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 4)
      (cast ((high64 >>! 20l <: u64) &. 31uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 5)
      (cast ((high64 >>! 25l <: u64) &. 31uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 6)
      (cast ((high64 >>! 30l <: u64) &. 31uL <: u64) <: i16)
  in
  let high:t_Array i16 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
      (sz 7)
      (cast ((high64 >>! 35l <: u64) &. 31uL <: u64) <: i16)
  in
  {
    f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize low <: t_Slice i16);
    f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize high <: t_Slice i16)
  }
  <:
  t_SIMD128Vector

let from_i16_array (array: t_Slice i16) =
  {
    f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (array.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16);
    f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (array.[ {
            Core.Ops.Range.f_start = sz 8;
            Core.Ops.Range.f_end = sz 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  }
  <:
  t_SIMD128Vector

let inv_ntt_layer_1_step (v: t_SIMD128Vector) (zeta1 zeta2 zeta3 zeta4: i16) =
  let zetas:t_Array i16 (sz 8) =
    let list = [zeta1; zeta1; zeta3; zeta3; zeta2; zeta2; zeta4; zeta4] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let zeta:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize zetas <: t_Slice i16)
  in
  let a:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v.f_low <: u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v.f_high <: u8)
        <:
        u8)
  in
  let b:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v.f_low <: u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v.f_high <: u8)
        <:
        u8)
  in
  let b_minus_a:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 b a in
  let a:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 a b in
  let a:u8 = barrett_reduce_int16x8_t a in
  let b:u8 = montgomery_multiply_int16x8_t b_minus_a zeta in
  let v:t_SIMD128Vector =
    {
      v with
      f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 b <: u8)
          <:
          u8)
    }
    <:
    t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    {
      v with
      f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 b <: u8)
          <:
          u8)
    }
    <:
    t_SIMD128Vector
  in
  v

let inv_ntt_layer_2_step (v: t_SIMD128Vector) (zeta1 zeta2: i16) =
  let zetas:t_Array i16 (sz 8) =
    let list = [zeta1; zeta1; zeta1; zeta1; zeta2; zeta2; zeta2; zeta2] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let zeta:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize zetas <: t_Slice i16)
  in
  let a:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s64
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v.f_low <: u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v.f_high <: u8)
        <:
        u8)
  in
  let b:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s64
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v.f_low <: u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v.f_high <: u8)
        <:
        u8)
  in
  let b_minus_a:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 b a in
  let a:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 a b in
  let b:u8 = montgomery_multiply_int16x8_t b_minus_a zeta in
  let v:t_SIMD128Vector =
    {
      v with
      f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s64
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 b <: u8)
          <:
          u8)
    }
    <:
    t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    {
      v with
      f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s64
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 b <: u8)
          <:
          u8)
    }
    <:
    t_SIMD128Vector
  in
  v

let inv_ntt_layer_3_step (v: t_SIMD128Vector) (zeta: i16) =
  let zeta:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 zeta in
  let b_minus_a:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 v.f_high v.f_low in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 v.f_low v.f_high }
    <:
    t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = montgomery_multiply_int16x8_t b_minus_a zeta } <: t_SIMD128Vector
  in
  v

let montgomery_multiply_by_constant (v: t_SIMD128Vector) (c: i16) =
  let v:t_SIMD128Vector =
    { v with f_low = montgomery_multiply_by_constant_int16x8_t v.f_low c } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = montgomery_multiply_by_constant_int16x8_t v.f_high c } <: t_SIMD128Vector
  in
  v

let multiply_by_constant (v: t_SIMD128Vector) (c: i16) =
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_intrinsics.Arm64_extract.v__vmulq_n_s16 v.f_low c } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_intrinsics.Arm64_extract.v__vmulq_n_s16 v.f_high c }
    <:
    t_SIMD128Vector
  in
  v

let ntt_layer_1_step (v: t_SIMD128Vector) (zeta1 zeta2 zeta3 zeta4: i16) =
  let zetas:t_Array i16 (sz 8) =
    let list = [zeta1; zeta1; zeta3; zeta3; zeta2; zeta2; zeta4; zeta4] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let zeta:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize zetas <: t_Slice i16)
  in
  let dup_a:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v.f_low <: u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v.f_high <: u8)
        <:
        u8)
  in
  let dup_b:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v.f_low <: u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v.f_high <: u8)
        <:
        u8)
  in
  let t:u8 = montgomery_multiply_int16x8_t dup_b zeta in
  let b:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 dup_a t in
  let a:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 dup_a t in
  let v:t_SIMD128Vector =
    {
      v with
      f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 b <: u8)
          <:
          u8)
    }
    <:
    t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    {
      v with
      f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 b <: u8)
          <:
          u8)
    }
    <:
    t_SIMD128Vector
  in
  v

let ntt_layer_2_step (v: t_SIMD128Vector) (zeta1 zeta2: i16) =
  let zetas:t_Array i16 (sz 8) =
    let list = [zeta1; zeta1; zeta1; zeta1; zeta2; zeta2; zeta2; zeta2] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let zeta:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize zetas <: t_Slice i16)
  in
  let dup_a:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s64
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v.f_low <: u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v.f_high <: u8)
        <:
        u8)
  in
  let dup_b:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s64
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v.f_low <: u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v.f_high <: u8)
        <:
        u8)
  in
  let t:u8 = montgomery_multiply_int16x8_t dup_b zeta in
  let b:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 dup_a t in
  let a:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 dup_a t in
  let v:t_SIMD128Vector =
    {
      v with
      f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s64
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 b <: u8)
          <:
          u8)
    }
    <:
    t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    {
      v with
      f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s64
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 b <: u8)
          <:
          u8)
    }
    <:
    t_SIMD128Vector
  in
  v

let ntt_layer_3_step (v: t_SIMD128Vector) (zeta: i16) =
  let zeta:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 zeta in
  let t:u8 = montgomery_multiply_int16x8_t v.f_high zeta in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 v.f_low t } <: t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 v.f_low t } <: t_SIMD128Vector
  in
  v

let ntt_multiply (lhs rhs: t_SIMD128Vector) (zeta1 zeta2 zeta3 zeta4: i16) =
  let (zetas: t_Array i16 (sz 8)):t_Array i16 (sz 8) =
    let list =
      [
        zeta1;
        zeta3;
        Core.Ops.Arith.Neg.neg zeta1;
        Core.Ops.Arith.Neg.neg zeta3;
        zeta2;
        zeta4;
        Core.Ops.Arith.Neg.neg zeta2;
        Core.Ops.Arith.Neg.neg zeta4
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let zeta:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize zetas <: t_Slice i16)
  in
  let a0:u8 = Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 lhs.f_low lhs.f_high in
  let a1:u8 = Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16 lhs.f_low lhs.f_high in
  let b0:u8 = Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 rhs.f_low rhs.f_high in
  let b1:u8 = Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16 rhs.f_low rhs.f_high in
  let a1b1:u8 = montgomery_multiply_int16x8_t a1 b1 in
  let a1b1_low:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vmull_s16 (Libcrux_intrinsics.Arm64_extract.v__vget_low_s16 a1b1

        <:
        u8)
      (Libcrux_intrinsics.Arm64_extract.v__vget_low_s16 zeta <: u8)
  in
  let a1b1_high:u8 = Libcrux_intrinsics.Arm64_extract.v__vmull_high_s16 a1b1 zeta in
  let fst_low:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vmlal_s16
          a1b1_low
          (Libcrux_intrinsics.Arm64_extract.v__vget_low_s16 a0 <: u8)
          (Libcrux_intrinsics.Arm64_extract.v__vget_low_s16 b0 <: u8)
        <:
        u8)
  in
  let fst_high:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vmlal_high_s16
          a1b1_high
          a0
          b0
        <:
        u8)
  in
  let a0b1_low:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vmull_s16 (Libcrux_intrinsics.Arm64_extract.v__vget_low_s16 a0

        <:
        u8)
      (Libcrux_intrinsics.Arm64_extract.v__vget_low_s16 b1 <: u8)
  in
  let a0b1_high:u8 = Libcrux_intrinsics.Arm64_extract.v__vmull_high_s16 a0 b1 in
  let snd_low:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vmlal_s16
          a0b1_low
          (Libcrux_intrinsics.Arm64_extract.v__vget_low_s16 a1 <: u8)
          (Libcrux_intrinsics.Arm64_extract.v__vget_low_s16 b0 <: u8)
        <:
        u8)
  in
  let snd_high:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vmlal_high_s16
          a0b1_high
          a1
          b0
        <:
        u8)
  in
  let fst_low16:u8 = Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 fst_low fst_high in
  let fst_high16:u8 = Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16 fst_low fst_high in
  let snd_low16:u8 = Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 snd_low snd_high in
  let snd_high16:u8 = Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16 snd_low snd_high in
  let fst:u8 = montgomery_reduce_int16x8_t fst_low16 fst_high16 in
  let snd:u8 = montgomery_reduce_int16x8_t snd_low16 snd_high16 in
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16
          fst
          snd
        <:
        u8)
  in
  let high0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16
          fst
          snd
        <:
        u8)
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
          low0
          high0
        <:
        u8)
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
          low0
          high0
        <:
        u8)
  in
  let (indexes: t_Array u8 (sz 16)):t_Array u8 (sz 16) =
    let list =
      [0uy; 1uy; 2uy; 3uy; 8uy; 9uy; 10uy; 11uy; 4uy; 5uy; 6uy; 7uy; 12uy; 13uy; 14uy; 15uy]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  in
  let index:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_u8 (Rust_primitives.unsize indexes <: t_Slice u8)
  in
  let low2:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u8 (Libcrux_intrinsics.Arm64_extract.v__vqtbl1q_u8
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u8_s16 low1 <: u8)
          index
        <:
        u8)
  in
  let high2:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_u8 (Libcrux_intrinsics.Arm64_extract.v__vqtbl1q_u8
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u8_s16 high1 <: u8)
          index
        <:
        u8)
  in
  { f_low = low2; f_high = high2 } <: t_SIMD128Vector

let serialize_1_ (v: t_SIMD128Vector) =
  let (shifter: t_Array i16 (sz 8)):t_Array i16 (sz 8) =
    let list = [0s; 1s; 2s; 3s; 4s; 5s; 6s; 7s] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let shift:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize shifter <: t_Slice i16)
  in
  let low:u8 = Libcrux_intrinsics.Arm64_extract.v__vshlq_s16 v.f_low shift in
  let high:u8 = Libcrux_intrinsics.Arm64_extract.v__vshlq_s16 v.f_high shift in
  let low:i16 = Libcrux_intrinsics.Arm64_extract.v__vaddvq_s16 low in
  let high:i16 = Libcrux_intrinsics.Arm64_extract.v__vaddvq_s16 high in
  let list = [cast (low <: i16) <: u8; cast (high <: i16) <: u8] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let serialize_10_ (v: t_SIMD128Vector) =
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16
          v.f_low
          v.f_low
        <:
        u8)
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16
          v.f_low
          v.f_low
        <:
        u8)
  in
  let mixt:u8 = Libcrux_intrinsics.Arm64_extract.v__vsliq_n_s32 10l low0 low1 in
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
          mixt
          mixt
        <:
        u8)
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
          mixt
          mixt
        <:
        u8)
  in
  let low_mix:u8 = Libcrux_intrinsics.Arm64_extract.v__vsliq_n_s64 20l low0 low1 in
  let high0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16
          v.f_high
          v.f_high
        <:
        u8)
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16
          v.f_high
          v.f_high
        <:
        u8)
  in
  let mixt:u8 = Libcrux_intrinsics.Arm64_extract.v__vsliq_n_s32 10l high0 high1 in
  let high0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
          mixt
          mixt
        <:
        u8)
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
          mixt
          mixt
        <:
        u8)
  in
  let high_mix:u8 = Libcrux_intrinsics.Arm64_extract.v__vsliq_n_s64 20l high0 high1 in
  let result32:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let result32:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result32
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Arm64_extract.v__vst1q_u8 (result32.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = sz 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u8_s64 low_mix <: u8)
        <:
        t_Slice u8)
  in
  let result32:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result32
      ({ Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 32 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Arm64_extract.v__vst1q_u8 (result32.[ {
                Core.Ops.Range.f_start = sz 16;
                Core.Ops.Range.f_end = sz 32
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u8_s64 high_mix <: u8)
        <:
        t_Slice u8)
  in
  let result:t_Array u8 (sz 20) = Rust_primitives.Hax.repeat 0uy (sz 20) in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (result.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (result32.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
      ({ Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 10 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (result.[ { Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 10 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (result32.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 13 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
      ({ Core.Ops.Range.f_start = sz 10; Core.Ops.Range.f_end = sz 15 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (result.[ { Core.Ops.Range.f_start = sz 10; Core.Ops.Range.f_end = sz 15 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (result32.[ { Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 21 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
      ({ Core.Ops.Range.f_start = sz 15; Core.Ops.Range.f_end = sz 20 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (result.[ { Core.Ops.Range.f_start = sz 15; Core.Ops.Range.f_end = sz 20 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (result32.[ { Core.Ops.Range.f_start = sz 24; Core.Ops.Range.f_end = sz 29 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  result

let serialize_12_ (v: t_SIMD128Vector) =
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16
          v.f_low
          v.f_low
        <:
        u8)
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16
          v.f_low
          v.f_low
        <:
        u8)
  in
  let mixt:u8 = Libcrux_intrinsics.Arm64_extract.v__vsliq_n_s32 12l low0 low1 in
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
          mixt
          mixt
        <:
        u8)
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
          mixt
          mixt
        <:
        u8)
  in
  let low_mix:u8 = Libcrux_intrinsics.Arm64_extract.v__vsliq_n_s64 24l low0 low1 in
  let high0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16
          v.f_high
          v.f_high
        <:
        u8)
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16
          v.f_high
          v.f_high
        <:
        u8)
  in
  let mixt:u8 = Libcrux_intrinsics.Arm64_extract.v__vsliq_n_s32 12l high0 high1 in
  let high0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
          mixt
          mixt
        <:
        u8)
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
          mixt
          mixt
        <:
        u8)
  in
  let high_mix:u8 = Libcrux_intrinsics.Arm64_extract.v__vsliq_n_s64 24l high0 high1 in
  let result32:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let result32:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result32
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Arm64_extract.v__vst1q_u8 (result32.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = sz 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u8_s64 low_mix <: u8)
        <:
        t_Slice u8)
  in
  let result32:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result32
      ({ Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 32 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Arm64_extract.v__vst1q_u8 (result32.[ {
                Core.Ops.Range.f_start = sz 16;
                Core.Ops.Range.f_end = sz 32
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u8_s64 high_mix <: u8)
        <:
        t_Slice u8)
  in
  let result:t_Array u8 (sz 24) = Rust_primitives.Hax.repeat 0uy (sz 24) in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 6 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (result.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 6 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (result32.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 6 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
      ({ Core.Ops.Range.f_start = sz 6; Core.Ops.Range.f_end = sz 12 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (result.[ { Core.Ops.Range.f_start = sz 6; Core.Ops.Range.f_end = sz 12 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (result32.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 14 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
      ({ Core.Ops.Range.f_start = sz 12; Core.Ops.Range.f_end = sz 18 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (result.[ { Core.Ops.Range.f_start = sz 12; Core.Ops.Range.f_end = sz 18 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (result32.[ { Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 22 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
      ({ Core.Ops.Range.f_start = sz 18; Core.Ops.Range.f_end = sz 24 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (result.[ { Core.Ops.Range.f_start = sz 18; Core.Ops.Range.f_end = sz 24 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (result32.[ { Core.Ops.Range.f_start = sz 24; Core.Ops.Range.f_end = sz 30 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  result

let serialize_4_ (v: t_SIMD128Vector) =
  let (shifter: t_Array i16 (sz 8)):t_Array i16 (sz 8) =
    let list = [0s; 4s; 8s; 12s; 0s; 4s; 8s; 12s] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let shift:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize shifter <: t_Slice i16)
  in
  let lowt:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshlq_u16 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_s16
          v.f_low
        <:
        u8)
      shift
  in
  let hight:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshlq_u16 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_s16
          v.f_high
        <:
        u8)
      shift
  in
  let sum0:u64 =
    cast (Libcrux_intrinsics.Arm64_extract.v__vaddv_u16 (Libcrux_intrinsics.Arm64_extract.v__vget_low_u16
              lowt
            <:
            u8)
        <:
        u16)
    <:
    u64
  in
  let sum1:u64 =
    cast (Libcrux_intrinsics.Arm64_extract.v__vaddv_u16 (Libcrux_intrinsics.Arm64_extract.v__vget_high_u16
              lowt
            <:
            u8)
        <:
        u16)
    <:
    u64
  in
  let sum2:u64 =
    cast (Libcrux_intrinsics.Arm64_extract.v__vaddv_u16 (Libcrux_intrinsics.Arm64_extract.v__vget_low_u16
              hight
            <:
            u8)
        <:
        u16)
    <:
    u64
  in
  let sum3:u64 =
    cast (Libcrux_intrinsics.Arm64_extract.v__vaddv_u16 (Libcrux_intrinsics.Arm64_extract.v__vget_high_u16
              hight
            <:
            u8)
        <:
        u16)
    <:
    u64
  in
  let sum:u64 =
    ((sum0 |. (sum1 <<! 16l <: u64) <: u64) |. (sum2 <<! 32l <: u64) <: u64) |.
    (sum3 <<! 48l <: u64)
  in
  Core.Num.impl__u64__to_le_bytes sum

let shift_right (v_SHIFT_BY: i32) (v: t_SIMD128Vector) =
  let v:t_SIMD128Vector =
    { v with f_low = Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 v_SHIFT_BY v.f_low }
    <:
    t_SIMD128Vector
  in
  let v:t_SIMD128Vector =
    { v with f_high = Libcrux_intrinsics.Arm64_extract.v__vshrq_n_s16 v_SHIFT_BY v.f_high }
    <:
    t_SIMD128Vector
  in
  v

let sub (lhs rhs: t_SIMD128Vector) =
  let lhs:t_SIMD128Vector =
    { lhs with f_low = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 lhs.f_low rhs.f_low }
    <:
    t_SIMD128Vector
  in
  let lhs:t_SIMD128Vector =
    { lhs with f_high = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 lhs.f_high rhs.f_high }
    <:
    t_SIMD128Vector
  in
  lhs

let to_i16_array (v: t_SIMD128Vector) =
  let out:t_Array i16 (sz 16) = Rust_primitives.Hax.repeat 0s (sz 16) in
  let out:t_Array i16 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Arm64_extract.v__vst1q_s16 (out.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = sz 8
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
          v.f_low
        <:
        t_Slice i16)
  in
  let out:t_Array i16 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({ Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Arm64_extract.v__vst1q_s16 (out.[ {
                Core.Ops.Range.f_start = sz 8;
                Core.Ops.Range.f_end = sz 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
          v.f_high
        <:
        t_Slice i16)
  in
  out

let serialize_11_ (v: t_SIMD128Vector) =
  let input:t_Array i16 (sz 16) = to_i16_array v in
  let result:t_Array u8 (sz 22) = Rust_primitives.Hax.repeat 0uy (sz 22) in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast (input.[ sz 0 ] <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((input.[ sz 0 ] <: i16) >>! 8l <: i16) |. ((input.[ sz 1 ] <: i16) <<! 3l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast (((input.[ sz 1 ] <: i16) >>! 5l <: i16) |. ((input.[ sz 2 ] <: i16) <<! 6l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast ((input.[ sz 2 ] <: i16) >>! 2l <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((input.[ sz 2 ] <: i16) >>! 10l <: i16) |. ((input.[ sz 3 ] <: i16) <<! 1l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast (((input.[ sz 3 ] <: i16) >>! 7l <: i16) |. ((input.[ sz 4 ] <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (cast (((input.[ sz 4 ] <: i16) >>! 4l <: i16) |. ((input.[ sz 5 ] <: i16) <<! 7l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast ((input.[ sz 5 ] <: i16) >>! 1l <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (cast (((input.[ sz 5 ] <: i16) >>! 9l <: i16) |. ((input.[ sz 6 ] <: i16) <<! 2l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast (((input.[ sz 6 ] <: i16) >>! 6l <: i16) |. ((input.[ sz 7 ] <: i16) <<! 5l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast ((input.[ sz 7 ] <: i16) >>! 3l <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 0 <: usize)
      (cast (input.[ sz 8 +! sz 0 <: usize ] <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 1 <: usize)
      (cast (((input.[ sz 8 +! sz 0 <: usize ] <: i16) >>! 8l <: i16) |.
            ((input.[ sz 8 +! sz 1 <: usize ] <: i16) <<! 3l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 2 <: usize)
      (cast (((input.[ sz 8 +! sz 1 <: usize ] <: i16) >>! 5l <: i16) |.
            ((input.[ sz 8 +! sz 2 <: usize ] <: i16) <<! 6l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 3 <: usize)
      (cast ((input.[ sz 8 +! sz 2 <: usize ] <: i16) >>! 2l <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 4 <: usize)
      (cast (((input.[ sz 8 +! sz 2 <: usize ] <: i16) >>! 10l <: i16) |.
            ((input.[ sz 8 +! sz 3 <: usize ] <: i16) <<! 1l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 5 <: usize)
      (cast (((input.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 7l <: i16) |.
            ((input.[ sz 8 +! sz 4 <: usize ] <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 6 <: usize)
      (cast (((input.[ sz 8 +! sz 4 <: usize ] <: i16) >>! 4l <: i16) |.
            ((input.[ sz 8 +! sz 5 <: usize ] <: i16) <<! 7l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 7 <: usize)
      (cast ((input.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 1l <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 8 <: usize)
      (cast (((input.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 9l <: i16) |.
            ((input.[ sz 8 +! sz 6 <: usize ] <: i16) <<! 2l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 9 <: usize)
      (cast (((input.[ sz 8 +! sz 6 <: usize ] <: i16) >>! 6l <: i16) |.
            ((input.[ sz 8 +! sz 7 <: usize ] <: i16) <<! 5l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11 +! sz 10 <: usize)
      (cast ((input.[ sz 8 +! sz 7 <: usize ] <: i16) >>! 3l <: i16) <: u8)
  in
  result

let serialize_5_ (v: t_SIMD128Vector) =
  let res:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
  let out:t_Array i16 (sz 16) = to_i16_array v in
  let res:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
      (sz 0)
      (cast ((out.[ sz 0 ] <: i16) |. ((out.[ sz 1 ] <: i16) <<! 5l <: i16) <: i16) <: u8)
  in
  let res:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
      (sz 1)
      (cast ((((out.[ sz 1 ] <: i16) >>! 3l <: i16) |. ((out.[ sz 2 ] <: i16) <<! 2l <: i16) <: i16) |.
            ((out.[ sz 3 ] <: i16) <<! 7l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let res:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
      (sz 2)
      (cast (((out.[ sz 3 ] <: i16) >>! 1l <: i16) |. ((out.[ sz 4 ] <: i16) <<! 4l <: i16) <: i16)
        <:
        u8)
  in
  let res:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
      (sz 3)
      (cast ((((out.[ sz 4 ] <: i16) >>! 4l <: i16) |. ((out.[ sz 5 ] <: i16) <<! 1l <: i16) <: i16) |.
            ((out.[ sz 6 ] <: i16) <<! 6l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let res:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
      (sz 4)
      (cast (((out.[ sz 6 ] <: i16) >>! 2l <: i16) |. ((out.[ sz 7 ] <: i16) <<! 3l <: i16) <: i16)
        <:
        u8)
  in
  let res:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
      (sz 5)
      (cast ((out.[ sz 8 +! sz 0 <: usize ] <: i16) |.
            ((out.[ sz 8 +! sz 1 <: usize ] <: i16) <<! 5l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let res:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
      (sz 6)
      (cast ((((out.[ sz 8 +! sz 1 <: usize ] <: i16) >>! 3l <: i16) |.
              ((out.[ sz 8 +! sz 2 <: usize ] <: i16) <<! 2l <: i16)
              <:
              i16) |.
            ((out.[ sz 8 +! sz 3 <: usize ] <: i16) <<! 7l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let res:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
      (sz 7)
      (cast (((out.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 1l <: i16) |.
            ((out.[ sz 8 +! sz 4 <: usize ] <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let res:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
      (sz 8)
      (cast ((((out.[ sz 8 +! sz 4 <: usize ] <: i16) >>! 4l <: i16) |.
              ((out.[ sz 8 +! sz 5 <: usize ] <: i16) <<! 1l <: i16)
              <:
              i16) |.
            ((out.[ sz 8 +! sz 6 <: usize ] <: i16) <<! 6l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let res:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
      (sz 9)
      (cast (((out.[ sz 8 +! sz 6 <: usize ] <: i16) >>! 2l <: i16) |.
            ((out.[ sz 8 +! sz 7 <: usize ] <: i16) <<! 3l <: i16)
            <:
            i16)
        <:
        u8)
  in
  res
