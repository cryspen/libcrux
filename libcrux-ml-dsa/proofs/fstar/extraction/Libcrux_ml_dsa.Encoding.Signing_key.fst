module Libcrux_ml_dsa.Encoding.Signing_key
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let generate_serialized
      (#v_SIMDUnit #v_Shake256: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (seed_for_A seed_for_signing verification_key: t_Slice u8)
      (s1: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      (s2 t0: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
     =
  let signing_key_serialized:t_Array u8 v_SIGNING_KEY_SIZE =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) v_SIGNING_KEY_SIZE
  in
  let offset:usize = Rust_primitives.mk_usize 0 in
  let signing_key_serialized:t_Array u8 v_SIGNING_KEY_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range signing_key_serialized
      ({
          Core.Ops.Range.f_start = offset;
          Core.Ops.Range.f_end = offset +! Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (signing_key_serialized.[ {
                Core.Ops.Range.f_start = offset;
                Core.Ops.Range.f_end = offset +! Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          seed_for_A
        <:
        t_Slice u8)
  in
  let offset:usize = offset +! Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE in
  let signing_key_serialized:t_Array u8 v_SIGNING_KEY_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range signing_key_serialized
      ({
          Core.Ops.Range.f_start = offset;
          Core.Ops.Range.f_end = offset +! Libcrux_ml_dsa.Constants.v_SEED_FOR_SIGNING_SIZE <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (signing_key_serialized.[ {
                Core.Ops.Range.f_start = offset;
                Core.Ops.Range.f_end
                =
                offset +! Libcrux_ml_dsa.Constants.v_SEED_FOR_SIGNING_SIZE <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          seed_for_signing
        <:
        t_Slice u8)
  in
  let offset:usize = offset +! Libcrux_ml_dsa.Constants.v_SEED_FOR_SIGNING_SIZE in
  let verification_key_hash:t_Array u8 (Rust_primitives.mk_usize 64) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 64)
  in
  let verification_key_hash:t_Array u8 (Rust_primitives.mk_usize 64) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256 #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.mk_usize 64)
      verification_key
      verification_key_hash
  in
  let signing_key_serialized:t_Array u8 v_SIGNING_KEY_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range signing_key_serialized
      ({
          Core.Ops.Range.f_start = offset;
          Core.Ops.Range.f_end
          =
          offset +! Libcrux_ml_dsa.Constants.v_BYTES_FOR_VERIFICATION_KEY_HASH <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (signing_key_serialized.[ {
                Core.Ops.Range.f_start = offset;
                Core.Ops.Range.f_end
                =
                offset +! Libcrux_ml_dsa.Constants.v_BYTES_FOR_VERIFICATION_KEY_HASH <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (verification_key_hash <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let offset:usize = offset +! Libcrux_ml_dsa.Constants.v_BYTES_FOR_VERIFICATION_KEY_HASH in
  let offset, signing_key_serialized:(usize & t_Array u8 v_SIGNING_KEY_SIZE) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              (s1 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
            <:
            Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (offset, signing_key_serialized <: (usize & t_Array u8 v_SIGNING_KEY_SIZE))
      (fun temp_0_ ring_element ->
          let offset, signing_key_serialized:(usize & t_Array u8 v_SIGNING_KEY_SIZE) = temp_0_ in
          let ring_element:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            ring_element
          in
          let signing_key_serialized:t_Array u8 v_SIGNING_KEY_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range signing_key_serialized
              ({
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end = offset +! v_ERROR_RING_ELEMENT_SIZE <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (signing_key_serialized.[ {
                        Core.Ops.Range.f_start = offset;
                        Core.Ops.Range.f_end = offset +! v_ERROR_RING_ELEMENT_SIZE <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_dsa.Encoding.Error.serialize #v_SIMDUnit
                      v_ETA
                      v_ERROR_RING_ELEMENT_SIZE
                      ring_element
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! v_ERROR_RING_ELEMENT_SIZE in
          offset, signing_key_serialized <: (usize & t_Array u8 v_SIGNING_KEY_SIZE))
  in
  let offset, signing_key_serialized:(usize & t_Array u8 v_SIGNING_KEY_SIZE) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              (s2 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
            <:
            Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (offset, signing_key_serialized <: (usize & t_Array u8 v_SIGNING_KEY_SIZE))
      (fun temp_0_ ring_element ->
          let offset, signing_key_serialized:(usize & t_Array u8 v_SIGNING_KEY_SIZE) = temp_0_ in
          let ring_element:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            ring_element
          in
          let signing_key_serialized:t_Array u8 v_SIGNING_KEY_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range signing_key_serialized
              ({
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end = offset +! v_ERROR_RING_ELEMENT_SIZE <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (signing_key_serialized.[ {
                        Core.Ops.Range.f_start = offset;
                        Core.Ops.Range.f_end = offset +! v_ERROR_RING_ELEMENT_SIZE <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_dsa.Encoding.Error.serialize #v_SIMDUnit
                      v_ETA
                      v_ERROR_RING_ELEMENT_SIZE
                      ring_element
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! v_ERROR_RING_ELEMENT_SIZE in
          offset, signing_key_serialized <: (usize & t_Array u8 v_SIGNING_KEY_SIZE))
  in
  let offset, signing_key_serialized:(usize & t_Array u8 v_SIGNING_KEY_SIZE) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              (t0 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
            <:
            Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (offset, signing_key_serialized <: (usize & t_Array u8 v_SIGNING_KEY_SIZE))
      (fun temp_0_ ring_element ->
          let offset, signing_key_serialized:(usize & t_Array u8 v_SIGNING_KEY_SIZE) = temp_0_ in
          let ring_element:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            ring_element
          in
          let signing_key_serialized:t_Array u8 v_SIGNING_KEY_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range signing_key_serialized
              ({
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end
                  =
                  offset +! Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T0S_SIZE <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (signing_key_serialized.[ {
                        Core.Ops.Range.f_start = offset;
                        Core.Ops.Range.f_end
                        =
                        offset +! Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T0S_SIZE <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_dsa.Encoding.T0.serialize #v_SIMDUnit ring_element <: t_Slice u8)
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T0S_SIZE in
          offset, signing_key_serialized <: (usize & t_Array u8 v_SIGNING_KEY_SIZE))
  in
  signing_key_serialized

let deserialize_then_ntt
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (serialized: t_Array u8 v_SIGNING_KEY_SIZE)
     =
  let seed_for_A, remaining_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (serialized <: t_Slice u8)
      Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE
  in
  let seed_for_signing, remaining_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      remaining_serialized
      Libcrux_ml_dsa.Constants.v_SEED_FOR_SIGNING_SIZE
  in
  let verification_key_hash, remaining_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      remaining_serialized
      Libcrux_ml_dsa.Constants.v_BYTES_FOR_VERIFICATION_KEY_HASH
  in
  let s1_serialized, remaining_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      remaining_serialized
      (v_ERROR_RING_ELEMENT_SIZE *! v_COLUMNS_IN_A <: usize)
  in
  let s2_serialized, t0_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      remaining_serialized
      (v_ERROR_RING_ELEMENT_SIZE *! v_ROWS_IN_A <: usize)
  in
  let s1_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_COLUMNS_IN_A =
    Libcrux_ml_dsa.Encoding.Error.deserialize_to_vector_then_ntt #v_SIMDUnit
      v_COLUMNS_IN_A
      v_ETA
      v_ERROR_RING_ELEMENT_SIZE
      s1_serialized
  in
  let s2_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Libcrux_ml_dsa.Encoding.Error.deserialize_to_vector_then_ntt #v_SIMDUnit
      v_ROWS_IN_A
      v_ETA
      v_ERROR_RING_ELEMENT_SIZE
      s2_serialized
  in
  let t0_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Libcrux_ml_dsa.Encoding.T0.deserialize_to_vector_then_ntt #v_SIMDUnit v_ROWS_IN_A t0_serialized
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
  Core.Result.impl__unwrap #(t_Array u8 (Rust_primitives.mk_usize 32))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (Rust_primitives.mk_usize 32))
        #FStar.Tactics.Typeclasses.solve
        seed_for_signing
      <:
      Core.Result.t_Result (t_Array u8 (Rust_primitives.mk_usize 32)) Core.Array.t_TryFromSliceError
    ),
  Core.Result.impl__unwrap #(t_Array u8 (Rust_primitives.mk_usize 64))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (Rust_primitives.mk_usize 64))
        #FStar.Tactics.Typeclasses.solve
        verification_key_hash
      <:
      Core.Result.t_Result (t_Array u8 (Rust_primitives.mk_usize 64)) Core.Array.t_TryFromSliceError
    ),
  s1_as_ntt,
  s2_as_ntt,
  t0_as_ntt
  <:
  (t_Array u8 (Rust_primitives.mk_usize 32) & t_Array u8 (Rust_primitives.mk_usize 32) &
    t_Array u8 (Rust_primitives.mk_usize 64) &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
