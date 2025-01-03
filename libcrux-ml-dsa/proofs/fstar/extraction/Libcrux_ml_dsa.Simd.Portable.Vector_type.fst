module Libcrux_ml_dsa.Simd.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_PortableSIMDUnit

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_PortableSIMDUnit

let impl_1 = impl_1'

let zero (_: Prims.unit) = Rust_primitives.Hax.repeat 0l (sz 8)

let from_coefficient_array (array: t_Slice i32) (out: t_Array i32 (sz 8)) =
  let hax_temp_output, out:(Prims.unit & t_Array i32 (sz 8)) =
    (),
    Core.Slice.impl__copy_from_slice #i32
      out
      (array.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i32)
    <:
    (Prims.unit & t_Array i32 (sz 8))
  in
  out

let to_coefficient_array (value: t_Array i32 (sz 8)) (out: t_Slice i32) =
  let out:t_Slice i32 = Core.Slice.impl__copy_from_slice #i32 out (value <: t_Slice i32) in
  out
