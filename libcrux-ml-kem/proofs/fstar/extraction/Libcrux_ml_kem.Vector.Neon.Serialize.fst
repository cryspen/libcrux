module Libcrux_ml_kem.Vector.Neon.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vandq_s16 low one;
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vandq_s16 high one
  }
  <:
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

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
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize low <: t_Slice i16);
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize high <: t_Slice i16)
  }
  <:
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

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
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize low <: t_Slice i16);
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize high <: t_Slice i16)
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
  {
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low = low;
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high = high
  }
  <:
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

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
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize low <: t_Slice i16);
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize high <: t_Slice i16)
  }
  <:
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

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
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_low
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize low <: t_Slice i16);
    Libcrux_ml_kem.Vector.Neon.Vector_type.f_high
    =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize high <: t_Slice i16)
  }
  <:
  Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

let serialize_1_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let (shifter: t_Array i16 (sz 8)):t_Array i16 (sz 8) =
    let list = [0s; 1s; 2s; 3s; 4s; 5s; 6s; 7s] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  let shift:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize shifter <: t_Slice i16)
  in
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
  let shift:u8 =
    Libcrux_intrinsics.Arm64_extract.v__vld1q_s16 (Rust_primitives.unsize shifter <: t_Slice i16)
  in
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

let serialize_11_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let input:t_Array i16 (sz 16) = Libcrux_ml_kem.Vector.Neon.Vector_type.to_i16_array v in
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

let serialize_5_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) =
  let res:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
  let out:t_Array i16 (sz 16) = Libcrux_ml_kem.Vector.Neon.Vector_type.to_i16_array v in
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
