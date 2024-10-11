module Libcrux_ml_dsa.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let serialize__OUTPUT_BYTES_PER_SIMD_UNIT: usize = Rust_primitives.mk_usize 4

let serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1: usize = Rust_primitives.mk_usize 6

let serialize
      (#v_SIMDUnit: Type0)
      (v_OUTPUT_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) v_OUTPUT_SIZE
  in
  match cast (v_OUTPUT_SIZE <: usize) <: u8 with
  | 128 ->
    let serialized:t_Array u8 v_OUTPUT_SIZE =
      Rust_primitives.Hax.Folds.fold_enumerated_slice (re.Libcrux_ml_dsa.Polynomial.f_simd_units
          <:
          t_Slice v_SIMDUnit)
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
            let _:usize = temp_1_ in
            true)
        serialized
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
            let i, simd_unit:(usize & v_SIMDUnit) = temp_1_ in
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = i *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT <: usize;
                  Core.Ops.Range.f_end
                  =
                  (i +! Rust_primitives.mk_usize 1 <: usize) *!
                  serialize__OUTPUT_BYTES_PER_SIMD_UNIT
                  <:
                  usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (serialized.[ {
                        Core.Ops.Range.f_start = i *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! Rust_primitives.mk_usize 1 <: usize) *!
                        serialize__OUTPUT_BYTES_PER_SIMD_UNIT
                        <:
                        usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_dsa.Simd.Traits.f_commitment_serialize #v_SIMDUnit
                      #FStar.Tactics.Typeclasses.solve
                      (Rust_primitives.mk_usize 4)
                      simd_unit
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_OUTPUT_SIZE)
    in
    serialized
  | 192 ->
    let serialized:t_Array u8 v_OUTPUT_SIZE =
      Rust_primitives.Hax.Folds.fold_enumerated_slice (re.Libcrux_ml_dsa.Polynomial.f_simd_units
          <:
          t_Slice v_SIMDUnit)
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
            let _:usize = temp_1_ in
            true)
        serialized
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
            let i, simd_unit:(usize & v_SIMDUnit) = temp_1_ in
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = i *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1 <: usize;
                  Core.Ops.Range.f_end
                  =
                  (i +! Rust_primitives.mk_usize 1 <: usize) *!
                  serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1
                  <:
                  usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (serialized.[ {
                        Core.Ops.Range.f_start
                        =
                        i *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1 <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! Rust_primitives.mk_usize 1 <: usize) *!
                        serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1
                        <:
                        usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_dsa.Simd.Traits.f_commitment_serialize #v_SIMDUnit
                      #FStar.Tactics.Typeclasses.solve
                      (Rust_primitives.mk_usize 6)
                      simd_unit
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_OUTPUT_SIZE)
    in
    serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let serialize_vector
      (#v_SIMDUnit: Type0)
      (v_DIMENSION v_RING_ELEMENT_SIZE v_OUTPUT_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (vector: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) v_OUTPUT_SIZE
  in
  let (offset: usize):usize = Rust_primitives.mk_usize 0 in
  let offset, serialized:(usize & t_Array u8 v_OUTPUT_SIZE) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              (vector <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
            <:
            Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (offset, serialized <: (usize & t_Array u8 v_OUTPUT_SIZE))
      (fun temp_0_ ring_element ->
          let offset, serialized:(usize & t_Array u8 v_OUTPUT_SIZE) = temp_0_ in
          let ring_element:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            ring_element
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end = offset +! v_RING_ELEMENT_SIZE <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (serialized.[ {
                        Core.Ops.Range.f_start = offset;
                        Core.Ops.Range.f_end = offset +! v_RING_ELEMENT_SIZE <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (serialize #v_SIMDUnit v_RING_ELEMENT_SIZE ring_element <: t_Slice u8)
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! v_RING_ELEMENT_SIZE in
          offset, serialized <: (usize & t_Array u8 v_OUTPUT_SIZE))
  in
  serialized
