module Libcrux_ml_kem.Vector.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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

let to_i16_array (x: t_PortableVector) = x.f_elements

let zero (_: Prims.unit) =
  { f_elements = Rust_primitives.Hax.repeat 0s (sz 16) } <: t_PortableVector
