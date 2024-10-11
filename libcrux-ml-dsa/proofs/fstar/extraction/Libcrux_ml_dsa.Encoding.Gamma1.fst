module Libcrux_ml_dsa.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let serialize__OUTPUT_BYTES_PER_SIMD_UNIT: usize = Rust_primitives.mk_usize 18

let serialize__OUTPUT_BYTES_PER_SIMD_UNIT_1: usize = Rust_primitives.mk_usize 20

let serialize
      (#v_SIMDUnit: Type0)
      (v_GAMMA1_EXPONENT v_OUTPUT_BYTES: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : t_Array u8 v_OUTPUT_BYTES =
  let serialized:t_Array u8 v_OUTPUT_BYTES =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) v_OUTPUT_BYTES
  in
  match cast (v_GAMMA1_EXPONENT <: usize) <: u8 with
  | 17 ->
    let serialized:t_Array u8 v_OUTPUT_BYTES =
      Rust_primitives.Hax.Folds.fold_enumerated_slice (re.Libcrux_ml_dsa.Polynomial.f_simd_units
          <:
          t_Slice v_SIMDUnit)
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_BYTES = serialized in
            let _:usize = temp_1_ in
            true)
        serialized
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_BYTES = serialized in
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
                  (Libcrux_ml_dsa.Simd.Traits.f_gamma1_serialize #v_SIMDUnit
                      #FStar.Tactics.Typeclasses.solve
                      (Rust_primitives.mk_usize 18)
                      simd_unit
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_OUTPUT_BYTES)
    in
    serialized
  | 19 ->
    let serialized:t_Array u8 v_OUTPUT_BYTES =
      Rust_primitives.Hax.Folds.fold_enumerated_slice (re.Libcrux_ml_dsa.Polynomial.f_simd_units
          <:
          t_Slice v_SIMDUnit)
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_BYTES = serialized in
            let _:usize = temp_1_ in
            true)
        serialized
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_BYTES = serialized in
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
                  (Libcrux_ml_dsa.Simd.Traits.f_gamma1_serialize #v_SIMDUnit
                      #FStar.Tactics.Typeclasses.solve
                      (Rust_primitives.mk_usize 20)
                      simd_unit
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_OUTPUT_BYTES)
    in
    serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize
      (#v_SIMDUnit: Type0)
      (v_GAMMA1_EXPONENT: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (serialized: t_Slice u8)
    : Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
  let serialized_chunks:Core.Slice.Iter.t_Chunks u8 =
    match cast (v_GAMMA1_EXPONENT <: usize) <: u8 with
    | 17 -> Core.Slice.impl__chunks #u8 serialized (Rust_primitives.mk_usize 18)
    | 19 -> Core.Slice.impl__chunks #u8 serialized (Rust_primitives.mk_usize 20)
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
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
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
                (Libcrux_ml_dsa.Simd.Traits.f_gamma1_deserialize #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    v_GAMMA1_EXPONENT
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
