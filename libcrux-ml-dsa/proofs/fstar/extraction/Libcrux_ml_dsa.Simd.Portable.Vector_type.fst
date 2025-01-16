module Libcrux_ml_dsa.Simd.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_Coefficients

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_Coefficients

let impl_1 = impl_1'

let zero (_: Prims.unit) = { f_values = Rust_primitives.Hax.repeat 0l (sz 8) } <: t_Coefficients

let from_coefficient_array (array: t_Slice i32) (out: t_Coefficients) =
  let out:t_Coefficients =
    {
      out with
      f_values
      =
      Core.Slice.impl__copy_from_slice #i32
        out.f_values
        (array.[ {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
            }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice i32)
    }
    <:
    t_Coefficients
  in
  out

let to_coefficient_array (value: t_Coefficients) (out: t_Slice i32) =
  let out:t_Slice i32 = Core.Slice.impl__copy_from_slice #i32 out (value.f_values <: t_Slice i32) in
  out
