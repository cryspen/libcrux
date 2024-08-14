module Libcrux_ml_kem.Vector.Neon.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_ZERO (_: Prims.unit) =
  {
    f_low = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 0s;
    f_high = Libcrux_intrinsics.Arm64_extract.v__vdupq_n_s16 0s
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
