module Libcrux_ml_dsa.Simd.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_ZERO (_: Prims.unit) =
  {
    f_coefficients
    =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_i32 0) (Rust_primitives.mk_usize 8)
  }
  <:
  t_PortableSIMDUnit

let from_coefficient_array (array: t_Slice i32) =
  {
    f_coefficients
    =
    Core.Result.impl__unwrap #(t_Array i32 (Rust_primitives.mk_usize 8))
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice i32)
          #(t_Array i32 (Rust_primitives.mk_usize 8))
          #FStar.Tactics.Typeclasses.solve
          (array.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
                Core.Ops.Range.f_end = Rust_primitives.mk_usize 8
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i32)
        <:
        Core.Result.t_Result (t_Array i32 (Rust_primitives.mk_usize 8))
          Core.Array.t_TryFromSliceError)
  }
  <:
  t_PortableSIMDUnit

let to_coefficient_array (x: t_PortableSIMDUnit) =
  Core.Result.impl__unwrap #(t_Array i32 (Rust_primitives.mk_usize 8))
    #Core.Convert.t_Infallible
    (Core.Convert.f_try_into #(t_Array i32 (Rust_primitives.mk_usize 8))
        #(t_Array i32 (Rust_primitives.mk_usize 8))
        #FStar.Tactics.Typeclasses.solve
        x.f_coefficients
      <:
      Core.Result.t_Result (t_Array i32 (Rust_primitives.mk_usize 8)) Core.Convert.t_Infallible)
