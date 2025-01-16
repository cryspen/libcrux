module Libcrux_ml_dsa.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let serialize
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (serialized: t_Slice u8)
     =
  let output_bytes_per_simd_unit:usize =
    (Core.Slice.impl__len #u8 serialized <: usize) /! (sz 8 *! sz 4 <: usize)
  in
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
            (Libcrux_ml_dsa.Simd.Traits.f_commitment_serialize #v_SIMDUnit
                #FStar.Tactics.Typeclasses.solve
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
  serialized

let serialize_vector
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (ring_element_size: usize)
      (vector: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (serialized: t_Slice u8)
     =
  let (offset: usize):usize = sz 0 in
  let offset, serialized:(usize & t_Slice u8) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              vector
            <:
            Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (offset, serialized <: (usize & t_Slice u8))
      (fun temp_0_ ring_element ->
          let offset, serialized:(usize & t_Slice u8) = temp_0_ in
          let ring_element:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            ring_element
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end = offset +! ring_element_size <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (serialize #v_SIMDUnit
                  ring_element
                  (serialized.[ {
                        Core.Ops.Range.f_start = offset;
                        Core.Ops.Range.f_end = offset +! ring_element_size <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! ring_element_size in
          offset, serialized <: (usize & t_Slice u8))
  in
  serialized
