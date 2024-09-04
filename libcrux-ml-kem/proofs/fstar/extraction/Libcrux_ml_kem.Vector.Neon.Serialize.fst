module Libcrux_ml_kem.Vector.Neon.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable in
  ()

let deserialize_1_ (a: t_Slice u8) =
  let one:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 1s in
  let low:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 (cast (a.[ sz 0 ] <: u8) <: i16) in
  let high:u8 = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 (cast (a.[ sz 1 ] <: u8) <: i16) in
  let (shifter: t_Array i16 (sz 8)):t_Array i16 (sz 8) =
    let list = [0s; 255s; (-2s); (-3s); (-4s); (-5s); (-6s); (-7s)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let shift:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (shifter <: t_Slice i16) in
  let low:u8 = Libcrux_intrinsics.Arm64_extract.v__vshlq_s16 low shift in
  let high:u8 = Libcrux_intrinsics.Arm64_extract.v__vshlq_s16 high shift in
  {
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vandq_s16 low one;
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vandq_s16 high one
  }
  <:
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

let deserialize_12_ (v: t_Slice u8) =
  let (indexes: t_Array u8 (sz 16)):t_Array u8 (sz 16) =
    let list =
      [0uy; 1uy; 1uy; 2uy; 3uy; 4uy; 4uy; 5uy; 6uy; 7uy; 7uy; 8uy; 9uy; 10uy; 10uy; 11uy]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  in
  let index_vec:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_u8 (indexes <: t_Slice u8) in
  let (shifts: t_Array i16 (sz 8)):t_Array i16 (sz 8) =
    let list = [0s; (-4s); 0s; (-4s); 0s; (-4s); 0s; (-4s)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let shift_vec:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (shifts <: t_Slice i16) in
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
  let input_vec0:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_u8 (input0 <: t_Slice u8) in
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
  let input_vec1:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_u8 (input1 <: t_Slice u8) in
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
  {
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low = low;
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high = high
  }
  <:
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

let serialize_1_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let (shifter: t_Array i16 (sz 8)):t_Array i16 (sz 8) =
    let list = [0s; 1s; 2s; 3s; 4s; 5s; 6s; 7s] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let shift:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (shifter <: t_Slice i16) in
  let low:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshlq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
      shift
  in
  let high:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshlq_s16 v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
      shift
  in
  let low:i16 = Libcrux_intrinsics.Arm64_extract.v__vaddvq_s16 low in
  let high:i16 = Libcrux_intrinsics.Arm64_extract.v__vaddvq_s16 high in
  let list = [cast (low <: i16) <: u8; cast (high <: i16) <: u8] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let serialize_10_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        <:
        u8)
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
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
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        <:
        u8)
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
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

let serialize_12_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let low0:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn1q_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        <:
        u8)
  in
  let low1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
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
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
        <:
        u8)
  in
  let high1:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_s32_s16 (Libcrux_intrinsics.Arm64_extract.v__vtrn2q_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
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

let serialize_4_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let (shifter: t_Array i16 (sz 8)):t_Array i16 (sz 8) =
    let list = [0s; 4s; 8s; 12s; 0s; 4s; 8s; 12s] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let shift:u8 = Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (shifter <: t_Slice i16) in
  let lowt:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshlq_u16 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
        <:
        u8)
      shift
  in
  let hight:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vshlq_u16 (Libcrux_intrinsics.Arm64_extract.v__vreinterpretq_u16_s16
          v.Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
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

let deserialize_10_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Traits.f_deserialize_10_ #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      v
  in
  let array:t_Array i16 (sz 16) =
    Libcrux_ml_kem.Vector.Traits.f_to_i16_array #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      output
  in
  {
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (array.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16);
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
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
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

let deserialize_11_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Traits.f_deserialize_11_ #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      v
  in
  let array:t_Array i16 (sz 16) =
    Libcrux_ml_kem.Vector.Traits.f_to_i16_array #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      output
  in
  {
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (array.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16);
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
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
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

let deserialize_4_ (v: t_Slice u8) =
  let input:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Traits.f_deserialize_4_ #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      v
  in
  let input_i16s:t_Array i16 (sz 16) =
    Libcrux_ml_kem.Vector.Traits.f_to_i16_array #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      input
  in
  {
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (input_i16s.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16);
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (input_i16s.[ {
            Core.Ops.Range.f_start = sz 8;
            Core.Ops.Range.f_end = sz 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  }
  <:
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

let deserialize_5_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Traits.f_deserialize_5_ #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      v
  in
  let array:t_Array i16 (sz 16) =
    Libcrux_ml_kem.Vector.Traits.f_to_i16_array #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      output
  in
  {
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (array.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16);
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
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
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

let serialize_11_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let out_i16s:t_Array i16 (sz 16) = Libcrux_ml_kem.Vector.Neon.Vector_type.to_i16_array v in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Traits.f_from_i16_array #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      (out_i16s <: t_Slice i16)
  in
  Libcrux_ml_kem.Vector.Traits.f_serialize_11_ #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #FStar.Tactics.Typeclasses.solve
    out

let serialize_5_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let out_i16s:t_Array i16 (sz 16) = Libcrux_ml_kem.Vector.Neon.Vector_type.to_i16_array v in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Traits.f_from_i16_array #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      (out_i16s <: t_Slice i16)
  in
  Libcrux_ml_kem.Vector.Traits.f_serialize_5_ #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #FStar.Tactics.Typeclasses.solve
    out
