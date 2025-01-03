module Libcrux_ml_dsa.Encoding.T1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let deserialize
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (serialized: t_Slice u8)
      (result: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i1.f_Coefficient
          (result.Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice i1.f_Coefficient)
        <:
        usize)
      (fun result temp_1_ ->
          let result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = result in
          let i:usize = i in
          {
            result with
            Libcrux_ml_dsa.Polynomial.f_simd_units
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                .Libcrux_ml_dsa.Polynomial.f_simd_units
              i
              (Libcrux_ml_dsa.Simd.Traits.f_t1_deserialize #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  (serialized.[ {
                        Core.Ops.Range.f_start = i *! deserialize__WINDOW <: usize;
                        Core.Ops.Range.f_end = (i +! sz 1 <: usize) *! deserialize__WINDOW <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (result.Libcrux_ml_dsa.Polynomial.f_simd_units.[ i ] <: i1.f_Coefficient)
                <:
                i1.f_Coefficient)
            <:
            t_Array i1.f_Coefficient (sz 32)
          }
          <:
          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  result

let serialize
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let serialized:t_Array u8 (sz 320) = Rust_primitives.Hax.repeat 0uy (sz 320) in
  let serialized:t_Array u8 (sz 320) =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (re.Libcrux_ml_dsa.Polynomial.f_simd_units
        <:
        t_Slice i1.f_Coefficient)
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (sz 320) = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (sz 320) = serialized in
          let i, simd_unit:(usize & i1.f_Coefficient) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
            ({
                Core.Ops.Range.f_start = i *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT <: usize;
                Core.Ops.Range.f_end
                =
                (i +! sz 1 <: usize) *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
            (Libcrux_ml_dsa.Simd.Traits.f_t1_serialize #v_SIMDUnit
                #FStar.Tactics.Typeclasses.solve
                simd_unit
                (serialized.[ {
                      Core.Ops.Range.f_start = i *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! sz 1 <: usize) *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
          <:
          t_Array u8 (sz 320))
  in
  serialized
