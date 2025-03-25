module Libcrux_ml_kem.Vector.Neon.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let repr (x:t_SIMD128Vector) = admit()

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_SIMD128Vector

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_SIMD128Vector

let impl_1 = impl_1'

let to_i16_array (v: t_SIMD128Vector) =
  let out:t_Array i16 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_i16 0) (mk_usize 16) in
  let out:t_Array i16 (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 8 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Arm64_extract.e_vst1q_s16 (out.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 8
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
          v.f_low
        <:
        t_Slice i16)
  in
  let out:t_Array i16 (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({ Core.Ops.Range.f_start = mk_usize 8; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Arm64_extract.e_vst1q_s16 (out.[ {
                Core.Ops.Range.f_start = mk_usize 8;
                Core.Ops.Range.f_end = mk_usize 16
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

let from_i16_array (array: t_Slice i16) =
  {
    f_low
    =
    Libcrux_intrinsics.Arm64_extract.e_vld1q_s16 (array.[ {
            Core.Ops.Range.f_start = mk_usize 0;
            Core.Ops.Range.f_end = mk_usize 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16);
    f_high
    =
    Libcrux_intrinsics.Arm64_extract.e_vld1q_s16 (array.[ {
            Core.Ops.Range.f_start = mk_usize 8;
            Core.Ops.Range.f_end = mk_usize 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  }
  <:
  t_SIMD128Vector

let to_bytes (v: t_SIMD128Vector) (bytes: t_Slice u8) =
  let bytes:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Arm64_extract.e_vst1q_bytes (bytes.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          v.f_low
        <:
        t_Slice u8)
  in
  let bytes:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes
      ({ Core.Ops.Range.f_start = mk_usize 16; Core.Ops.Range.f_end = mk_usize 32 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Arm64_extract.e_vst1q_bytes (bytes.[ {
                Core.Ops.Range.f_start = mk_usize 16;
                Core.Ops.Range.f_end = mk_usize 32
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          v.f_high
        <:
        t_Slice u8)
  in
  bytes

let from_bytes (array: t_Slice u8) =
  {
    f_low
    =
    Libcrux_intrinsics.Arm64_extract.e_vld1q_bytes (array.[ {
            Core.Ops.Range.f_start = mk_usize 0;
            Core.Ops.Range.f_end = mk_usize 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8);
    f_high
    =
    Libcrux_intrinsics.Arm64_extract.e_vld1q_bytes (array.[ {
            Core.Ops.Range.f_start = mk_usize 16;
            Core.Ops.Range.f_end = mk_usize 32
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  }
  <:
  t_SIMD128Vector

let v_ZERO (_: Prims.unit) =
  {
    f_low = Libcrux_intrinsics.Arm64_extract.e_vdupq_n_s16 (mk_i16 0);
    f_high = Libcrux_intrinsics.Arm64_extract.e_vdupq_n_s16 (mk_i16 0)
  }
  <:
  t_SIMD128Vector
