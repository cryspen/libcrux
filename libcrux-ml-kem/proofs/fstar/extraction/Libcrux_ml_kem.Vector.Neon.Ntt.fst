module Libcrux_ml_kem.Vector.Neon.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let inv_ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (zeta1 zeta2 zeta3 zeta4: i16)
     =
  let zetas:t_Array i16 (sz 8) =
    let list = [zeta1; zeta1; zeta3; zeta3; zeta2; zeta2; zeta4; zeta4] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let zeta:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (zetas <: t_Slice i16) in
  let a:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
            <:
            u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
            <:
            u8)
        <:
        u8)
  in
  let b:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
            <:
            u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
            <:
            u8)
        <:
        u8)
  in
  let b_minus_a:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 b a in
  let a:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 a b in
  let a:u8 = Libcrux_ml_kem.Vector.Neon.Arithmetic.barrett_reduce_int16x8_t a in
  let b:u8 = Libcrux_ml_kem.Vector.Neon.Arithmetic.montgomery_multiply_int16x8_t b_minus_a zeta in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 b <: u8)
          <:
          u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 b <: u8)
          <:
          u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let inv_ntt_layer_2_step
      (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (zeta1 zeta2: i16)
     =
  let zetas:t_Array i16 (sz 8) =
    let list = [zeta1; zeta1; zeta1; zeta1; zeta2; zeta2; zeta2; zeta2] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let zeta:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (zetas <: t_Slice i16) in
  let a:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s64
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
            <:
            u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
            <:
            u8)
        <:
        u8)
  in
  let b:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s64
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
            <:
            u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
            <:
            u8)
        <:
        u8)
  in
  let b_minus_a:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 b a in
  let a:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 a b in
  let b:u8 = Libcrux_ml_kem.Vector.Neon.Arithmetic.montgomery_multiply_int16x8_t b_minus_a zeta in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s64
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 b <: u8)
          <:
          u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s64
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 b <: u8)
          <:
          u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let inv_ntt_layer_3_step (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta: i16) =
  let zeta:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 zeta in
  let b_minus_a:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_ml_kem.Vector.Neon.Arithmetic.montgomery_multiply_int16x8_t b_minus_a zeta
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (zeta1 zeta2 zeta3 zeta4: i16)
     =
  let zetas:t_Array i16 (sz 8) =
    let list = [zeta1; zeta1; zeta3; zeta3; zeta2; zeta2; zeta4; zeta4] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let zeta:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (zetas <: t_Slice i16) in
  let dup_a:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
            <:
            u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
            <:
            u8)
        <:
        u8)
  in
  let dup_b:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
            <:
            u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
            <:
            u8)
        <:
        u8)
  in
  let t:u8 = Libcrux_ml_kem.Vector.Neon.Arithmetic.montgomery_multiply_int16x8_t dup_b zeta in
  let b:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 dup_a t in
  let a:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 dup_a t in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s32
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 b <: u8)
          <:
          u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s32 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s32
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 b <: u8)
          <:
          u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let ntt_layer_2_step (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta1 zeta2: i16) =
  let zetas:t_Array i16 (sz 8) =
    let list = [zeta1; zeta1; zeta1; zeta1; zeta2; zeta2; zeta2; zeta2] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let zeta:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (zetas <: t_Slice i16) in
  let dup_a:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s64
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
            <:
            u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
            <:
            u8)
        <:
        u8)
  in
  let dup_b:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s64
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
            <:
            u8)
          (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 v
                .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
            <:
            u8)
        <:
        u8)
  in
  let t:u8 = Libcrux_ml_kem.Vector.Neon.Arithmetic.montgomery_multiply_int16x8_t dup_b zeta in
  let b:u8 = Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 dup_a t in
  let a:u8 = Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 dup_a t in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s64
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 b <: u8)
          <:
          u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s16_s64 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s64
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 a <: u8)
            (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s64_s16 b <: u8)
          <:
          u8)
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let ntt_layer_3_step (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta: i16) =
  let zeta:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 zeta in
  let t:u8 =
    Libcrux_ml_kem.Vector.Neon.Arithmetic.montgomery_multiply_int16x8_t v
        .Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      =
      Libcrux_intrinsics.Arm64_extract.v__vsubq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low t
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  let v:Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    {
      v with
      Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      =
      Libcrux_intrinsics.Arm64_extract.v__vaddq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low t
    }
    <:
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
  in
  v

let ntt_multiply
      (lhs rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (zeta1 zeta2 zeta3 zeta4: i16)
     =
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
  let zeta:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (zetas <: t_Slice i16) in
  let a0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 lhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      lhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
  in
  let a1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16 lhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      lhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
  in
  let b0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16 rhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      rhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
  in
  let b1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16 rhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      rhs.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
  in
  let a1b1:u8 = Libcrux_ml_kem.Vector.Neon.Arithmetic.montgomery_multiply_int16x8_t a1 b1 in
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
  let fst:u8 =
    Libcrux_ml_kem.Vector.Neon.Arithmetic.montgomery_reduce_int16x8_t fst_low16 fst_high16
  in
  let snd:u8 =
    Libcrux_ml_kem.Vector.Neon.Arithmetic.montgomery_reduce_int16x8_t snd_low16 snd_high16
  in
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
  let index:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_u8 (indexes <: t_Slice u8) in
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
  {
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low = low2;
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high = high2
  }
  <:
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
