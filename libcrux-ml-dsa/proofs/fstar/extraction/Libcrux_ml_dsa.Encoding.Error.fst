module Libcrux_ml_dsa.Encoding.Error
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
      (v_ETA v_OUTPUT_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let serialized:t_Array u8 v_OUTPUT_SIZE = Rust_primitives.Hax.repeat 0uy v_OUTPUT_SIZE in
  match cast (v_ETA <: usize) <: u8 with
  | 2uy ->
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
                  (i +! sz 1 <: usize) *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
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
                  (Libcrux_ml_dsa.Simd.Traits.f_error_serialize #v_SIMDUnit
                      #FStar.Tactics.Typeclasses.solve
                      (sz 3)
                      simd_unit
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_OUTPUT_SIZE)
    in
    serialized
  | 4uy ->
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
                  (i +! sz 1 <: usize) *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1 <: usize
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
                        (i +! sz 1 <: usize) *! serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_dsa.Simd.Traits.f_error_serialize #v_SIMDUnit
                      #FStar.Tactics.Typeclasses.solve
                      (sz 4)
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

let deserialize
      (#v_SIMDUnit: Type0)
      (v_ETA: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (serialized: t_Slice u8)
     =
  let serialized_chunks:Core.Slice.Iter.t_Chunks u8 =
    match cast (v_ETA <: usize) <: u8 with
    | 2uy -> Core.Slice.impl__chunks #u8 serialized (sz 3)
    | 4uy -> Core.Slice.impl__chunks #u8 serialized (sz 4)
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
  in
  let result, serialized_chunks:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Core.Slice.Iter.t_Chunks u8) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #v_SIMDUnit
          (result.Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let result, serialized_chunks:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement
            v_SIMDUnit &
            Core.Slice.Iter.t_Chunks u8) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (result, serialized_chunks
        <:
        (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & Core.Slice.Iter.t_Chunks u8)
      )
      (fun temp_0_ i ->
          let result, serialized_chunks:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement
            v_SIMDUnit &
            Core.Slice.Iter.t_Chunks u8) =
            temp_0_
          in
          let i:usize = i in
          let tmp0, out:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option (t_Slice u8)) =
            Core.Iter.Traits.Iterator.f_next #(Core.Slice.Iter.t_Chunks u8)
              #FStar.Tactics.Typeclasses.solve
              serialized_chunks
          in
          let serialized_chunks:Core.Slice.Iter.t_Chunks u8 = tmp0 in
          ({
              result with
              Libcrux_ml_dsa.Polynomial.f_simd_units
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                  .Libcrux_ml_dsa.Polynomial.f_simd_units
                i
                (Libcrux_ml_dsa.Simd.Traits.f_error_deserialize #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    v_ETA
                    (Core.Option.impl__unwrap #(t_Slice u8) out <: t_Slice u8)
                  <:
                  v_SIMDUnit)
            }
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit),
          serialized_chunks
          <:
          (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
            Core.Slice.Iter.t_Chunks u8))
  in
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
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Chunks u8))
          #FStar.Tactics.Typeclasses.solve
          (Core.Iter.Traits.Iterator.f_enumerate #(Core.Slice.Iter.t_Chunks u8)
              #FStar.Tactics.Typeclasses.solve
              (Core.Slice.impl__chunks #u8 serialized v_RING_ELEMENT_SIZE
                <:
                Core.Slice.Iter.t_Chunks u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
      ring_elements
      (fun ring_elements temp_1_ ->
          let ring_elements:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            ring_elements
          in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize ring_elements
            i
            (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
                (deserialize #v_SIMDUnit v_ETA bytes
                  <:
                  Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
  in
  ring_elements
