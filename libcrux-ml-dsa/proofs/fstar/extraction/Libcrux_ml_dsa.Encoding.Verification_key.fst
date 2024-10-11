module Libcrux_ml_dsa.Encoding.Verification_key
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let generate_serialized
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_VERIFICATION_KEY_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (seed_for_A: t_Slice u8)
      (t1: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
    : t_Array u8 v_VERIFICATION_KEY_SIZE =
  let verification_key_serialized:t_Array u8 v_VERIFICATION_KEY_SIZE =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) v_VERIFICATION_KEY_SIZE
  in
  let verification_key_serialized:t_Array u8 v_VERIFICATION_KEY_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range verification_key_serialized
      ({
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
          Core.Ops.Range.f_end = Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (verification_key_serialized.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
                Core.Ops.Range.f_end = Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          seed_for_A
        <:
        t_Slice u8)
  in
  let verification_key_serialized:t_Array u8 v_VERIFICATION_KEY_SIZE =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (t1
        <:
        t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (fun verification_key_serialized temp_1_ ->
          let verification_key_serialized:t_Array u8 v_VERIFICATION_KEY_SIZE =
            verification_key_serialized
          in
          let _:usize = temp_1_ in
          true)
      verification_key_serialized
      (fun verification_key_serialized temp_1_ ->
          let verification_key_serialized:t_Array u8 v_VERIFICATION_KEY_SIZE =
            verification_key_serialized
          in
          let i, ring_element:(usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          =
            temp_1_
          in
          let offset:usize =
            Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE +!
            (i *! Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T1S_SIZE <: usize)
          in
          let verification_key_serialized:t_Array u8 v_VERIFICATION_KEY_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range verification_key_serialized
              ({
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end
                  =
                  offset +! Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T1S_SIZE <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (verification_key_serialized.[ {
                        Core.Ops.Range.f_start = offset;
                        Core.Ops.Range.f_end
                        =
                        offset +! Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T1S_SIZE <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_dsa.Encoding.T1.serialize #v_SIMDUnit ring_element <: t_Slice u8)
                <:
                t_Slice u8)
          in
          verification_key_serialized)
  in
  verification_key_serialized

let deserialize
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_VERIFICATION_KEY_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
    : (t_Array u8 (Rust_primitives.mk_usize 32) &
      t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_ROWS_IN_A
  in
  let seed_for_A, serialized_remaining:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (serialized <: t_Slice u8)
      Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE
  in
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      v_ROWS_IN_A
      (fun t1 temp_1_ ->
          let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A
          =
            t1
          in
          let _:usize = temp_1_ in
          true)
      t1
      (fun t1 i ->
          let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A
          =
            t1
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1
            i
            (Libcrux_ml_dsa.Encoding.T1.deserialize #v_SIMDUnit
                (serialized_remaining.[ {
                      Core.Ops.Range.f_start
                      =
                      i *! Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T1S_SIZE <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! Rust_primitives.mk_usize 1 <: usize) *!
                      Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T1S_SIZE
                      <:
                      usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
  in
  Core.Result.impl__unwrap #(t_Array u8 (Rust_primitives.mk_usize 32))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (Rust_primitives.mk_usize 32))
        #FStar.Tactics.Typeclasses.solve
        seed_for_A
      <:
      Core.Result.t_Result (t_Array u8 (Rust_primitives.mk_usize 32)) Core.Array.t_TryFromSliceError
    ),
  t1
  <:
  (t_Array u8 (Rust_primitives.mk_usize 32) &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
