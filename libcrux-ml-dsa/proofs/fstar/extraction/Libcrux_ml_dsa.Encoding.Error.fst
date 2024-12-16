module Libcrux_ml_dsa.Encoding.Error
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
      (v_ETA: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (serialized: t_Slice u8)
      (result: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let chunk_size:usize = if v_ETA =. sz 2 then sz 3 else sz 4 in
  let result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #v_SIMDUnit
          (result.Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
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
              (Libcrux_ml_dsa.Simd.Traits.f_error_deserialize #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  v_ETA
                  (serialized.[ {
                        Core.Ops.Range.f_start = i *! chunk_size <: usize;
                        Core.Ops.Range.f_end = (i +! sz 1 <: usize) *! chunk_size <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (sz 32)
          }
          <:
          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  result

let deserialize_to_vector_then_ntt
      (#v_SIMDUnit: Type0)
      (v_DIMENSION v_ETA v_RING_ELEMENT_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (serialized: t_Slice u8)
     =
  let ring_elements:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_DIMENSION
  in
  let ring_elements:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_DIMENSION =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice v_RING_ELEMENT_SIZE
      serialized
      (fun ring_elements temp_1_ ->
          let ring_elements:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            ring_elements
          in
          let _:usize = temp_1_ in
          true)
      ring_elements
      (fun ring_elements temp_1_ ->
          let ring_elements:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            ring_elements
          in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let ring_elements:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize ring_elements
              i
              (deserialize #v_SIMDUnit
                  v_ETA
                  bytes
                  (ring_elements.[ i ]
                    <:
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let ring_elements:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize ring_elements
              i
              (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
                  (ring_elements.[ i ]
                    <:
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          ring_elements)
  in
  ring_elements

let serialize
      (#v_SIMDUnit: Type0)
      (v_ETA v_OUTPUT_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (serialized: t_Slice u8)
     =
  let output_bytes_per_simd_unit:usize = if v_ETA =. sz 2 then sz 3 else sz 4 in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (re.Libcrux_ml_dsa.Polynomial.f_simd_units
        <:
        t_Slice v_SIMDUnit)
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let i, simd_unit:(usize & v_SIMDUnit) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
            ({
                Core.Ops.Range.f_start = i *! output_bytes_per_simd_unit <: usize;
                Core.Ops.Range.f_end = (i +! sz 1 <: usize) *! output_bytes_per_simd_unit <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
            (Libcrux_ml_dsa.Simd.Traits.f_error_serialize #v_SIMDUnit
                #FStar.Tactics.Typeclasses.solve
                v_ETA
                simd_unit
                (serialized.[ {
                      Core.Ops.Range.f_start = i *! output_bytes_per_simd_unit <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! sz 1 <: usize) *! output_bytes_per_simd_unit <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
          <:
          t_Slice u8)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  serialized
