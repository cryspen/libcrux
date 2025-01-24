module Libcrux_ml_kem.Vector.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_PortableVector

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_PortableVector

let impl_1 = impl_1'

let zero (_: Prims.unit) =
  { f_elements = Rust_primitives.Hax.repeat 0s (sz 16) } <: t_PortableVector

let to_i16_array (x: t_PortableVector) = x.f_elements

let from_i16_array (array: t_Slice i16) =
  {
    f_elements
    =
    Core.Result.impl__unwrap #(t_Array i16 (sz 16))
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice i16)
          #(t_Array i16 (sz 16))
          #FStar.Tactics.Typeclasses.solve
          (array.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
        <:
        Core.Result.t_Result (t_Array i16 (sz 16)) Core.Array.t_TryFromSliceError)
  }
  <:
  t_PortableVector
