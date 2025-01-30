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
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (error_ring_element_size: usize)
      (seed_matrix seed_signing verification_key: t_Slice u8)
      (s1_2_ t0: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (signing_key_serialized: t_Slice u8)
     =
  let offset:usize = mk_usize 0 in
  let signing_key_serialized:t_Slice u8 =
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
          seed_matrix
        <:
        t_Slice u8)
  in
  let offset:usize = offset +! Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE in
  let signing_key_serialized:t_Slice u8 =
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
          seed_signing
        <:
        t_Slice u8)
  in
  let offset:usize = offset +! Libcrux_ml_dsa.Constants.v_SEED_FOR_SIGNING_SIZE in
  let verification_key_hash:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64)
  in
  let verification_key_hash:t_Array u8 (mk_usize 64) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256 #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      (mk_usize 64)
      verification_key
      verification_key_hash
  in
  let signing_key_serialized:t_Slice u8 =
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
  let offset, signing_key_serialized:(usize & t_Slice u8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) s1_2_
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let offset, signing_key_serialized:(usize & t_Slice u8) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (offset, signing_key_serialized <: (usize & t_Slice u8))
      (fun temp_0_ i ->
          let offset, signing_key_serialized:(usize & t_Slice u8) = temp_0_ in
          let i:usize = i in
          let signing_key_serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range signing_key_serialized
              ({
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end = offset +! error_ring_element_size <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Libcrux_ml_dsa.Encoding.Error.serialize #v_SIMDUnit
                  eta
                  (s1_2_.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  (signing_key_serialized.[ {
                        Core.Ops.Range.f_start = offset;
                        Core.Ops.Range.f_end = offset +! error_ring_element_size <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! error_ring_element_size in
          offset, signing_key_serialized <: (usize & t_Slice u8))
  in
  let offset, signing_key_serialized:(usize & t_Slice u8) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) t0
            <:
            Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (offset, signing_key_serialized <: (usize & t_Slice u8))
      (fun temp_0_ ring_element ->
          let offset, signing_key_serialized:(usize & t_Slice u8) = temp_0_ in
          let ring_element:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            ring_element
          in
          let signing_key_serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range signing_key_serialized
              ({
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end
                  =
                  offset +! Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T0S_SIZE <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Libcrux_ml_dsa.Encoding.T0.serialize #v_SIMDUnit
                  ring_element
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
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T0S_SIZE in
          offset, signing_key_serialized <: (usize & t_Slice u8))
  in
  signing_key_serialized
