module Libcrux_ml_dsa.Simd.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let from_coefficient_array (array: t_Slice i32) =
  {
    f_coefficients
    =
    Core.Result.impl__unwrap #(t_Array i32 (sz 8))
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice i32)
          #(t_Array i32 (sz 8))
          #FStar.Tactics.Typeclasses.solve
          (array.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i32)
        <:
        Core.Result.t_Result (t_Array i32 (sz 8)) Core.Array.t_TryFromSliceError)
  }
  <:
  t_PortableSIMDUnit

let to_coefficient_array (x: t_PortableSIMDUnit) = x.f_coefficients

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_PortableSIMDUnit

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_PortableSIMDUnit

let impl_1 = impl_1'

let v_ZERO (_: Prims.unit) =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 8) } <: t_PortableSIMDUnit
