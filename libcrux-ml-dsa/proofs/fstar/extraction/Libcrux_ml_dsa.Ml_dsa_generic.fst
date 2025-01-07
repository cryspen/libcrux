module Libcrux_ml_dsa.Ml_dsa_generic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Polynomial in
  let open Libcrux_ml_dsa.Pre_hash in
  let open Libcrux_ml_dsa.Samplex4 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let derive_message_representative
      (#v_Shake256Xof: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (verification_key_hash: t_Slice u8)
      (domain_separation_context:
          Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext)
      (message: t_Slice u8)
      (message_representative: t_Array u8 (sz 64))
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 verification_key_hash <: usize) =. sz 64 <: bool
          )
      in
      ()
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_init #v_Shake256Xof #FStar.Tactics.Typeclasses.solve ()
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      verification_key_hash
  in
  let shake:v_Shake256Xof =
    match
      domain_separation_context
      <:
      Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext
    with
    | Core.Option.Option_Some domain_separation_context ->
      let shake:v_Shake256Xof =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
          #FStar.Tactics.Typeclasses.solve
          shake
          ((let list =
                [
                  cast (Core.Option.impl__is_some #(t_Array u8 (sz 11))
                        (Libcrux_ml_dsa.Pre_hash.impl_1__pre_hash_oid domain_separation_context
                          <:
                          Core.Option.t_Option (t_Array u8 (sz 11)))
                      <:
                      bool)
                  <:
                  u8
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice u8)
      in
      let shake:v_Shake256Xof =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
          #FStar.Tactics.Typeclasses.solve
          shake
          ((let list =
                [
                  cast (Core.Slice.impl__len #u8
                        (Libcrux_ml_dsa.Pre_hash.impl_1__context domain_separation_context
                          <:
                          t_Slice u8)
                      <:
                      usize)
                  <:
                  u8
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice u8)
      in
      let shake:v_Shake256Xof =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
          #FStar.Tactics.Typeclasses.solve
          shake
          (Libcrux_ml_dsa.Pre_hash.impl_1__context domain_separation_context <: t_Slice u8)
      in
      (match
          Libcrux_ml_dsa.Pre_hash.impl_1__pre_hash_oid domain_separation_context
          <:
          Core.Option.t_Option (t_Array u8 (sz 11))
        with
        | Core.Option.Option_Some pre_hash_oid ->
          Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
            #FStar.Tactics.Typeclasses.solve
            shake
            (pre_hash_oid <: t_Slice u8)
        | _ -> shake)
    | _ -> shake
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb_final #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      message
  in
  let tmp0, tmp1:(v_Shake256Xof & t_Array u8 (sz 64)) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      message_representative
  in
  let shake:v_Shake256Xof = tmp0 in
  let message_representative:t_Array u8 (sz 64) = tmp1 in
  let _:Prims.unit = () in
  message_representative

let sign_internal
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT:
          usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i8:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i9:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i10:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i11:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message: t_Slice u8)
      (domain_separation_context:
          Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext)
      (randomness: t_Array u8 (sz 32))
     =
  let eta:Libcrux_ml_dsa.Constants.t_Eta =
    match cast (v_ETA <: usize) <: u8 with
    | 2uy -> Libcrux_ml_dsa.Constants.Eta_Two <: Libcrux_ml_dsa.Constants.t_Eta
    | 4uy -> Libcrux_ml_dsa.Constants.Eta_Four <: Libcrux_ml_dsa.Constants.t_Eta
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let seed_for_a, remaining_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (signing_key <: t_Slice u8)
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
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_COLUMNS_IN_A
  in
  let s2_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_ROWS_IN_A
  in
  let t0_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_ROWS_IN_A
  in
  let s1_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_COLUMNS_IN_A =
    Libcrux_ml_dsa.Encoding.Error.deserialize_to_vector_then_ntt #v_SIMDUnit
      eta
      v_ERROR_RING_ELEMENT_SIZE
      s1_serialized
      s1_as_ntt
  in
  let s2_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Libcrux_ml_dsa.Encoding.Error.deserialize_to_vector_then_ntt #v_SIMDUnit
      eta
      v_ERROR_RING_ELEMENT_SIZE
      s2_serialized
      s2_as_ntt
  in
  let t0_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Libcrux_ml_dsa.Encoding.T0.deserialize_to_vector_then_ntt #v_SIMDUnit t0_serialized t0_as_ntt
  in
  let matrix:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_X_COLUMNS
  =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_ROWS_X_COLUMNS
  in
  let matrix:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_X_COLUMNS
  =
    Libcrux_ml_dsa.Samplex4.f_matrix_flat #v_Sampler
      #FStar.Tactics.Typeclasses.solve
      #v_SIMDUnit
      v_COLUMNS_IN_A
      seed_for_a
      matrix
  in
  let message_representative:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
  let message_representative:t_Array u8 (sz 64) =
    derive_message_representative #v_Shake256Xof
      verification_key_hash
      domain_separation_context
      message
      message_representative
  in
  let mask_seed:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_init #v_Shake256Xof #FStar.Tactics.Typeclasses.solve ()
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      seed_for_signing
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      (randomness <: t_Slice u8)
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb_final #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      (message_representative <: t_Slice u8)
  in
  let tmp0, tmp1:(v_Shake256Xof & t_Array u8 (sz 64)) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      mask_seed
  in
  let shake:v_Shake256Xof = tmp0 in
  let mask_seed:t_Array u8 (sz 64) = tmp1 in
  let _:Prims.unit = () in
  let _:Prims.unit = () in
  let (domain_separator_for_mask: u16):u16 = 0us in
  let beta:i32 = cast (v_ONES_IN_VERIFIER_CHALLENGE *! v_ETA <: usize) <: i32 in
  let attempt:usize = sz 0 in
  let commitment_hash:Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) =
    Core.Option.Option_None <: Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE)
  in
  let signer_response:Core.Option.t_Option
  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A) =
    Core.Option.Option_None
    <:
    Core.Option.t_Option
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let hint:Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) =
    Core.Option.Option_None <: Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A)
  in
  let attempt, commitment_hash, domain_separator_for_mask, hint, signer_response:(usize &
    Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) &
    u16 &
    Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
    Core.Option.t_Option
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let attempt, commitment_hash, domain_separator_for_mask, hint, signer_response:(usize &
            Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) &
            u16 &
            Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
            Core.Option.t_Option
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A))
          =
            temp_0_
          in
          attempt <. Libcrux_ml_dsa.Constants.v_REJECTION_SAMPLE_BOUND_SIGN <: bool)
      (attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
        <:
        (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
          Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
          Core.Option.t_Option
          (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)))
      (fun temp_0_ ->
          let attempt, commitment_hash, domain_separator_for_mask, hint, signer_response:(usize &
            Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) &
            u16 &
            Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
            Core.Option.t_Option
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A))
          =
            temp_0_
          in
          let attempt:usize = attempt +! sz 1 in
          let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_COLUMNS_IN_A =
            Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              v_COLUMNS_IN_A
          in
          let w0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A
          =
            Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              v_ROWS_IN_A
          in
          let commitment:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              v_ROWS_IN_A
          in
          let tmp0, tmp1:(u16 &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A) =
            Libcrux_ml_dsa.Sample.sample_mask_vector #v_SIMDUnit
              #v_Shake256
              #v_Shake256X4
              v_COLUMNS_IN_A
              v_GAMMA1_EXPONENT
              mask_seed
              domain_separator_for_mask
              mask
          in
          let domain_separator_for_mask:u16 = tmp0 in
          let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_COLUMNS_IN_A =
            tmp1
          in
          let _:Prims.unit = () in
          let a_x_mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              v_ROWS_IN_A
          in
          let mask_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_COLUMNS_IN_A =
            Core.Clone.f_clone #(t_Array
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
              #FStar.Tactics.Typeclasses.solve
              mask
          in
          let mask_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_COLUMNS_IN_A =
            Rust_primitives.Hax.Folds.fold_range (sz 0)
              (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  (mask_ntt
                    <:
                    t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
                <:
                usize)
              (fun mask_ntt temp_1_ ->
                  let mask_ntt:t_Array
                    (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
                    mask_ntt
                  in
                  let _:usize = temp_1_ in
                  true)
              mask_ntt
              (fun mask_ntt i ->
                  let mask_ntt:t_Array
                    (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
                    mask_ntt
                  in
                  let i:usize = i in
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask_ntt
                    i
                    (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
                        (mask_ntt.[ i ]
                          <:
                          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                      <:
                      Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  <:
                  t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_COLUMNS_IN_A)
          in
          let a_x_mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Libcrux_ml_dsa.Matrix.compute_matrix_x_mask #v_SIMDUnit
              v_ROWS_IN_A
              v_COLUMNS_IN_A
              (matrix <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
              (mask_ntt <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
              a_x_mask
          in
          let tmp0, tmp1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              v_ROWS_IN_A &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
            Libcrux_ml_dsa.Arithmetic.decompose_vector #v_SIMDUnit
              v_ROWS_IN_A
              v_GAMMA2
              (a_x_mask <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
              w0
              commitment
          in
          let w0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A
          =
            tmp0
          in
          let commitment:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            tmp1
          in
          let _:Prims.unit = () in
          let _:Prims.unit = () in
          let commitment_hash_candidate:t_Array u8 v_COMMITMENT_HASH_SIZE =
            Rust_primitives.Hax.repeat 0uy v_COMMITMENT_HASH_SIZE
          in
          let commitment_serialized:t_Array u8 v_COMMITMENT_VECTOR_SIZE =
            Rust_primitives.Hax.repeat 0uy v_COMMITMENT_VECTOR_SIZE
          in
          let commitment_serialized:t_Array u8 v_COMMITMENT_VECTOR_SIZE =
            Libcrux_ml_dsa.Encoding.Commitment.serialize_vector #v_SIMDUnit
              v_COMMITMENT_RING_ELEMENT_SIZE
              (commitment <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
              commitment_serialized
          in
          let shake:v_Shake256Xof =
            Libcrux_ml_dsa.Hash_functions.Shake256.f_init #v_Shake256Xof
              #FStar.Tactics.Typeclasses.solve
              ()
          in
          let shake:v_Shake256Xof =
            Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
              #FStar.Tactics.Typeclasses.solve
              shake
              (message_representative <: t_Slice u8)
          in
          let shake:v_Shake256Xof =
            Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb_final #v_Shake256Xof
              #FStar.Tactics.Typeclasses.solve
              shake
              (commitment_serialized <: t_Slice u8)
          in
          let tmp0, tmp1:(v_Shake256Xof & t_Array u8 v_COMMITMENT_HASH_SIZE) =
            Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze #v_Shake256Xof
              #FStar.Tactics.Typeclasses.solve
              shake
              commitment_hash_candidate
          in
          let shake:v_Shake256Xof = tmp0 in
          let commitment_hash_candidate:t_Array u8 v_COMMITMENT_HASH_SIZE = tmp1 in
          let _:Prims.unit = () in
          let _:Prims.unit = () in
          let verifier_challenge:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
          in
          let verifier_challenge:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Libcrux_ml_dsa.Sample.sample_challenge_ring_element #v_SIMDUnit
              #v_Shake256
              (commitment_hash_candidate <: t_Slice u8)
              v_ONES_IN_VERIFIER_CHALLENGE
              verifier_challenge
          in
          let verifier_challenge:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit verifier_challenge
          in
          let challenge_times_s1:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
            Core.Clone.f_clone #(t_Array
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
              #FStar.Tactics.Typeclasses.solve
              s1_as_ntt
          in
          let challenge_times_s2:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
            Core.Clone.f_clone #(t_Array
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
              #FStar.Tactics.Typeclasses.solve
              s2_as_ntt
          in
          let challenge_times_s1:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
            Libcrux_ml_dsa.Matrix.vector_times_ring_element #v_SIMDUnit
              challenge_times_s1
              verifier_challenge
          in
          let challenge_times_s2:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
            Libcrux_ml_dsa.Matrix.vector_times_ring_element #v_SIMDUnit
              challenge_times_s2
              verifier_challenge
          in
          let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_COLUMNS_IN_A =
            Libcrux_ml_dsa.Matrix.add_vectors #v_SIMDUnit
              v_COLUMNS_IN_A
              mask
              (challenge_times_s1
                <:
                t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          in
          let w0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A
          =
            Libcrux_ml_dsa.Matrix.subtract_vectors #v_SIMDUnit
              v_ROWS_IN_A
              w0
              (challenge_times_s2
                <:
                t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          in
          if
            Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
              (mask <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
              ((1l <<! v_GAMMA1_EXPONENT <: i32) -! beta <: i32)
          then
            attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
            <:
            (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
              Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
              Core.Option.t_Option
              (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A
              ))
          else
            if
              Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
                (w0 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
                (v_GAMMA2 -! beta <: i32)
            then
              attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
              <:
              (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
                Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
                Core.Option.t_Option
                (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_COLUMNS_IN_A))
            else
              let challenge_times_t0:t_Array
                (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
                Core.Clone.f_clone #(t_Array
                      (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
                  #FStar.Tactics.Typeclasses.solve
                  t0_as_ntt
              in
              let challenge_times_t0:t_Array
                (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
                Libcrux_ml_dsa.Matrix.vector_times_ring_element #v_SIMDUnit
                  challenge_times_t0
                  verifier_challenge
              in
              if
                Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
                  (challenge_times_t0
                    <:
                    t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
                  v_GAMMA2
              then
                attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
                <:
                (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
                  Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
                  Core.Option.t_Option
                  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                      v_COLUMNS_IN_A))
              else
                let w0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  v_ROWS_IN_A =
                  Libcrux_ml_dsa.Matrix.add_vectors #v_SIMDUnit
                    v_ROWS_IN_A
                    w0
                    (challenge_times_t0
                      <:
                      t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
                in
                let hint_candidate:t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A =
                  Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0l (sz 256)
                      <:
                      t_Array i32 (sz 256))
                    v_ROWS_IN_A
                in
                let tmp0, out:(t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize) =
                  Libcrux_ml_dsa.Arithmetic.make_hint #v_SIMDUnit
                    v_ROWS_IN_A
                    v_GAMMA2
                    w0
                    commitment
                    hint_candidate
                in
                let hint_candidate:t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A = tmp0 in
                let ones_in_hint:usize = out in
                if ones_in_hint >. v_MAX_ONES_IN_HINT
                then
                  attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
                  <:
                  (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
                    Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
                    Core.Option.t_Option
                    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        v_COLUMNS_IN_A))
                else
                  let attempt:usize = Libcrux_ml_dsa.Constants.v_REJECTION_SAMPLE_BOUND_SIGN in
                  let commitment_hash:Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) =
                    Core.Option.Option_Some commitment_hash_candidate
                    <:
                    Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE)
                  in
                  let signer_response:Core.Option.t_Option
                  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                      v_COLUMNS_IN_A) =
                    Core.Option.Option_Some mask
                    <:
                    Core.Option.t_Option
                    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        v_COLUMNS_IN_A)
                  in
                  let hint:Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) =
                    Core.Option.Option_Some hint_candidate
                    <:
                    Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A)
                  in
                  attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
                  <:
                  (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
                    Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
                    Core.Option.t_Option
                    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        v_COLUMNS_IN_A)))
  in
  match commitment_hash <: Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) with
  | Core.Option.Option_Some commitment_hash ->
    let commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE = commitment_hash in
    (match
        signer_response
        <:
        Core.Option.t_Option
        (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      with
      | Core.Option.Option_Some signer_response ->
        let signer_response:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          v_COLUMNS_IN_A =
          signer_response
        in
        (match hint <: Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) with
          | Core.Option.Option_Some hint ->
            let hint:t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A = hint in
            let signature:t_Array u8 v_SIGNATURE_SIZE =
              Rust_primitives.Hax.repeat 0uy v_SIGNATURE_SIZE
            in
            let signature:t_Array u8 v_SIGNATURE_SIZE =
              Libcrux_ml_dsa.Encoding.Signature.serialize #v_SIMDUnit
                (commitment_hash <: t_Slice u8)
                (signer_response
                  <:
                  t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
                (hint <: t_Slice (t_Array i32 (sz 256))) v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A
                v_ROWS_IN_A v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_MAX_ONES_IN_HINT
                signature
            in
            Core.Result.Result_Ok (Libcrux_ml_dsa.Types.impl_4__new v_SIGNATURE_SIZE signature)
            <:
            Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
              Libcrux_ml_dsa.Types.t_SigningError
          | Core.Option.Option_None  ->
            Core.Result.Result_Err
            (Libcrux_ml_dsa.Types.SigningError_RejectionSamplingError
              <:
              Libcrux_ml_dsa.Types.t_SigningError)
            <:
            Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
              Libcrux_ml_dsa.Types.t_SigningError)
      | Core.Option.Option_None  ->
        Core.Result.Result_Err
        (Libcrux_ml_dsa.Types.SigningError_RejectionSamplingError
          <:
          Libcrux_ml_dsa.Types.t_SigningError)
        <:
        Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
          Libcrux_ml_dsa.Types.t_SigningError)
  | Core.Option.Option_None  ->
    Core.Result.Result_Err
    (Libcrux_ml_dsa.Types.SigningError_RejectionSamplingError <: Libcrux_ml_dsa.Types.t_SigningError
    )
    <:
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
      Libcrux_ml_dsa.Types.t_SigningError

let sign
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT:
          usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i8:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i9:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i10:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i11:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  match
    Libcrux_ml_dsa.Pre_hash.impl_1__new context
      (Core.Option.Option_None <: Core.Option.t_Option (t_Array u8 (sz 11)))
    <:
    Core.Result.t_Result Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext
      Libcrux_ml_dsa.Pre_hash.t_DomainSeparationError
  with
  | Core.Result.Result_Ok dsc ->
    let domain_separation_context:Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext = dsc in
    sign_internal #v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4
      v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT
      v_GAMMA2 v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
      v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE
      v_SIGNATURE_SIZE signing_key message
      (Core.Option.Option_Some domain_separation_context
        <:
        Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext) randomness
  | Core.Result.Result_Err _ ->
    Core.Result.Result_Err
    (Libcrux_ml_dsa.Types.SigningError_ContextTooLongError <: Libcrux_ml_dsa.Types.t_SigningError)
    <:
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
      Libcrux_ml_dsa.Types.t_SigningError

let sign_pre_hashed
      (#v_SIMDUnit #v_Sampler #v_Shake128 #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4 #v_PH:
          Type0)
      (v_PH_DIGEST_LEN v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT:
          usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i8:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i9: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i10:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i11:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i12:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i13:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i14:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i15:
          Libcrux_ml_dsa.Pre_hash.t_PreHash v_PH v_PH_DIGEST_LEN)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  if (Core.Slice.impl__len #u8 context <: usize) >. Libcrux_ml_dsa.Constants.v_CONTEXT_MAX_LEN
  then
    Core.Result.Result_Err
    (Libcrux_ml_dsa.Types.SigningError_ContextTooLongError <: Libcrux_ml_dsa.Types.t_SigningError)
    <:
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
      Libcrux_ml_dsa.Types.t_SigningError
  else
    let pre_hashed_message:t_Array u8 v_PH_DIGEST_LEN =
      Libcrux_ml_dsa.Pre_hash.f_hash #v_PH
        #v_PH_DIGEST_LEN
        #FStar.Tactics.Typeclasses.solve
        #v_Shake128
        message
    in
    match
      Libcrux_ml_dsa.Pre_hash.impl_1__new context
        (Core.Option.Option_Some
          (Libcrux_ml_dsa.Pre_hash.f_oid #v_PH #v_PH_DIGEST_LEN #FStar.Tactics.Typeclasses.solve ()
            <:
            t_Array u8 (sz 11))
          <:
          Core.Option.t_Option (t_Array u8 (sz 11)))
      <:
      Core.Result.t_Result Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext
        Libcrux_ml_dsa.Pre_hash.t_DomainSeparationError
    with
    | Core.Result.Result_Ok dsc ->
      let domain_separation_context:Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext = dsc in
      sign_internal #v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4
        v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE
        v_GAMMA1_EXPONENT v_GAMMA2 v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE
        v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT
        v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE signing_key
        (pre_hashed_message <: t_Slice u8)
        (Core.Option.Option_Some domain_separation_context
          <:
          Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext) randomness
    | Core.Result.Result_Err _ ->
      Core.Result.Result_Err
      (Libcrux_ml_dsa.Types.SigningError_ContextTooLongError <: Libcrux_ml_dsa.Types.t_SigningError)
      <:
      Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
        Libcrux_ml_dsa.Types.t_SigningError

let verify_internal
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i7:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i8:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i9:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (verification_key: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message: t_Slice u8)
      (domain_separation_context:
          Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
     =
  let seed_for_a, t1_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (verification_key <: t_Slice u8)
      Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE
  in
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_ROWS_IN_A
  in
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Libcrux_ml_dsa.Encoding.Verification_key.deserialize #v_SIMDUnit
      v_ROWS_IN_A
      v_VERIFICATION_KEY_SIZE
      t1_serialized
      t1
  in
  let deserialized_commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE =
    Rust_primitives.Hax.repeat 0uy v_COMMITMENT_HASH_SIZE
  in
  let deserialized_signer_response:t_Array
    (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_COLUMNS_IN_A
  in
  let deserialized_hint:t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0l (sz 256) <: t_Array i32 (sz 256))
      v_ROWS_IN_A
  in
  let tmp0, tmp1, tmp2, out:(t_Array u8 v_COMMITMENT_HASH_SIZE &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A &
    t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError) =
    Libcrux_ml_dsa.Encoding.Signature.deserialize #v_SIMDUnit v_COLUMNS_IN_A v_ROWS_IN_A
      v_COMMITMENT_HASH_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_MAX_ONES_IN_HINT
      v_SIGNATURE_SIZE (signature_serialized <: t_Slice u8) deserialized_commitment_hash
      deserialized_signer_response deserialized_hint
  in
  let deserialized_commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE = tmp0 in
  let deserialized_signer_response:t_Array
    (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
    tmp1
  in
  let deserialized_hint:t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A = tmp2 in
  match out <: Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError with
  | Core.Result.Result_Ok _ ->
    let _:Prims.unit = () <: Prims.unit in
    if
      Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
        (deserialized_signer_response
          <:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        ((2l <<! v_GAMMA1_EXPONENT <: i32) -! v_BETA <: i32)
    then
      Core.Result.Result_Err
      (Libcrux_ml_dsa.Types.VerificationError_SignerResponseExceedsBoundError
        <:
        Libcrux_ml_dsa.Types.t_VerificationError)
      <:
      Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError
    else
      let matrix:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
        v_ROWS_X_COLUMNS =
        Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          v_ROWS_X_COLUMNS
      in
      let matrix:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
        v_ROWS_X_COLUMNS =
        Libcrux_ml_dsa.Samplex4.f_matrix_flat #v_Sampler
          #FStar.Tactics.Typeclasses.solve
          #v_SIMDUnit
          v_COLUMNS_IN_A
          seed_for_a
          matrix
      in
      let verification_key_hash:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
      let verification_key_hash:t_Array u8 (sz 64) =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256 #v_Shake256
          #FStar.Tactics.Typeclasses.solve
          (sz 64)
          (verification_key <: t_Slice u8)
          verification_key_hash
      in
      let message_representative:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
      let message_representative:t_Array u8 (sz 64) =
        derive_message_representative #v_Shake256Xof
          (verification_key_hash <: t_Slice u8)
          domain_separation_context
          message
          message_representative
      in
      let verifier_challenge:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
        Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
      in
      let verifier_challenge:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
        Libcrux_ml_dsa.Sample.sample_challenge_ring_element #v_SIMDUnit
          #v_Shake256
          (deserialized_commitment_hash <: t_Slice u8)
          v_ONES_IN_VERIFIER_CHALLENGE
          verifier_challenge
      in
      let verifier_challenge:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
        Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit verifier_challenge
      in
      let deserialized_signer_response:t_Array
        (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
        Rust_primitives.Hax.Folds.fold_range (sz 0)
          (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              (deserialized_signer_response
                <:
                t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
            <:
            usize)
          (fun deserialized_signer_response temp_1_ ->
              let deserialized_signer_response:t_Array
                (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
                deserialized_signer_response
              in
              let _:usize = temp_1_ in
              true)
          deserialized_signer_response
          (fun deserialized_signer_response i ->
              let deserialized_signer_response:t_Array
                (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
                deserialized_signer_response
              in
              let i:usize = i in
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize deserialized_signer_response
                i
                (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
                    (deserialized_signer_response.[ i ]
                      <:
                      Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  <:
                  Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      in
      let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
        Libcrux_ml_dsa.Matrix.compute_w_approx #v_SIMDUnit
          v_ROWS_IN_A
          v_COLUMNS_IN_A
          (matrix <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          (deserialized_signer_response
            <:
            t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          verifier_challenge
          t1
      in
      let recomputed_commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE =
        Rust_primitives.Hax.repeat 0uy v_COMMITMENT_HASH_SIZE
      in
      let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
        Libcrux_ml_dsa.Arithmetic.use_hint #v_SIMDUnit
          v_GAMMA2
          (deserialized_hint <: t_Slice (t_Array i32 (sz 256)))
          t1
      in
      let commitment_serialized:t_Array u8 v_COMMITMENT_VECTOR_SIZE =
        Rust_primitives.Hax.repeat 0uy v_COMMITMENT_VECTOR_SIZE
      in
      let commitment_serialized:t_Array u8 v_COMMITMENT_VECTOR_SIZE =
        Libcrux_ml_dsa.Encoding.Commitment.serialize_vector #v_SIMDUnit
          v_COMMITMENT_RING_ELEMENT_SIZE
          (t1 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          commitment_serialized
      in
      let shake:v_Shake256Xof =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_init #v_Shake256Xof
          #FStar.Tactics.Typeclasses.solve
          ()
      in
      let shake:v_Shake256Xof =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
          #FStar.Tactics.Typeclasses.solve
          shake
          (message_representative <: t_Slice u8)
      in
      let shake:v_Shake256Xof =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb_final #v_Shake256Xof
          #FStar.Tactics.Typeclasses.solve
          shake
          (commitment_serialized <: t_Slice u8)
      in
      let tmp0, tmp1:(v_Shake256Xof & t_Array u8 v_COMMITMENT_HASH_SIZE) =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze #v_Shake256Xof
          #FStar.Tactics.Typeclasses.solve
          shake
          recomputed_commitment_hash
      in
      let shake:v_Shake256Xof = tmp0 in
      let recomputed_commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE = tmp1 in
      let _:Prims.unit = () in
      let _:Prims.unit = () in
      if deserialized_commitment_hash =. recomputed_commitment_hash
      then
        Core.Result.Result_Ok (() <: Prims.unit)
        <:
        Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError
      else
        Core.Result.Result_Err
        (Libcrux_ml_dsa.Types.VerificationError_CommitmentHashesDontMatchError
          <:
          Libcrux_ml_dsa.Types.t_VerificationError)
        <:
        Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError
  | Core.Result.Result_Err e ->
    Core.Result.Result_Err e
    <:
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError

let verify
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i7:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i8:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i9:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
     =
  match
    Libcrux_ml_dsa.Pre_hash.impl_1__new context
      (Core.Option.Option_None <: Core.Option.t_Option (t_Array u8 (sz 11)))
    <:
    Core.Result.t_Result Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext
      Libcrux_ml_dsa.Pre_hash.t_DomainSeparationError
  with
  | Core.Result.Result_Ok dsc ->
    let domain_separation_context:Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext = dsc in
    verify_internal #v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof v_ROWS_IN_A
      v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
      v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
      v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
      v_MAX_ONES_IN_HINT verification_key_serialized message
      (Core.Option.Option_Some domain_separation_context
        <:
        Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext) signature_serialized
  | Core.Result.Result_Err _ ->
    Core.Result.Result_Err
    (Libcrux_ml_dsa.Types.VerificationError_VerificationContextTooLongError
      <:
      Libcrux_ml_dsa.Types.t_VerificationError)
    <:
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError

let verify_pre_hashed
      (#v_SIMDUnit #v_Sampler #v_Shake128 #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_PH: Type0)
      (v_PH_DIGEST_LEN v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i7:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i8: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i9:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i10:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i11:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i12:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i13:
          Libcrux_ml_dsa.Pre_hash.t_PreHash v_PH v_PH_DIGEST_LEN)
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
     =
  let pre_hashed_message:t_Array u8 v_PH_DIGEST_LEN =
    Libcrux_ml_dsa.Pre_hash.f_hash #v_PH
      #v_PH_DIGEST_LEN
      #FStar.Tactics.Typeclasses.solve
      #v_Shake128
      message
  in
  match
    Libcrux_ml_dsa.Pre_hash.impl_1__new context
      (Core.Option.Option_Some
        (Libcrux_ml_dsa.Pre_hash.f_oid #v_PH #v_PH_DIGEST_LEN #FStar.Tactics.Typeclasses.solve ()
          <:
          t_Array u8 (sz 11))
        <:
        Core.Option.t_Option (t_Array u8 (sz 11)))
    <:
    Core.Result.t_Result Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext
      Libcrux_ml_dsa.Pre_hash.t_DomainSeparationError
  with
  | Core.Result.Result_Ok dsc ->
    let domain_separation_context:Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext = dsc in
    verify_internal #v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof v_ROWS_IN_A
      v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
      v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
      v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
      v_MAX_ONES_IN_HINT verification_key_serialized (pre_hashed_message <: t_Slice u8)
      (Core.Option.Option_Some domain_separation_context
        <:
        Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext) signature_serialized
  | Core.Result.Result_Err _ ->
    Core.Result.Result_Err
    (Libcrux_ml_dsa.Types.VerificationError_VerificationContextTooLongError
      <:
      Libcrux_ml_dsa.Types.t_VerificationError)
    <:
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError

let generate_key_pair_v44
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i8:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i9:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i10:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i11:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 signing_key <: usize) =.
            generate_key_pair_v44__SIGNING_KEY_SIZE
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 verification_key <: usize) =.
            generate_key_pair_v44__VERIFICATION_KEY_SIZE
            <:
            bool)
      in
      ()
  in
  let seed_expanded:t_Array u8 (sz 128) = Rust_primitives.Hax.repeat 0uy (sz 128) in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_init #v_Shake256Xof #FStar.Tactics.Typeclasses.solve ()
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      (randomness <: t_Slice u8)
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb_final #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      ((let list =
            [
              cast (generate_key_pair_v44__ROWS_IN_A <: usize) <: u8;
              cast (generate_key_pair_v44__COLUMNS_IN_A <: usize) <: u8
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice u8)
  in
  let tmp0, tmp1:(v_Shake256Xof & t_Array u8 (sz 128)) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      seed_expanded
  in
  let shake:v_Shake256Xof = tmp0 in
  let seed_expanded:t_Array u8 (sz 128) = tmp1 in
  let _:Prims.unit = () in
  let _:Prims.unit = () in
  let seed_for_a, seed_expanded:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (seed_expanded <: t_Slice u8)
      Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE
  in
  let seed_for_error_vectors, seed_for_signing:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      seed_expanded
      Libcrux_ml_dsa.Constants.v_SEED_FOR_ERROR_VECTORS_SIZE
  in
  let a_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 16) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 16)
  in
  let a_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 16) =
    Libcrux_ml_dsa.Samplex4.f_matrix_flat #v_Sampler
      #FStar.Tactics.Typeclasses.solve
      #v_SIMDUnit
      generate_key_pair_v44__COLUMNS_IN_A
      seed_for_a
      a_as_ntt
  in
  let s1_s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 8) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 8)
  in
  let s1_s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 8) =
    Libcrux_ml_dsa.Samplex4.sample_s1_and_s2 #v_SIMDUnit
      #v_Shake256X4
      generate_key_pair_v44__ETA
      seed_for_error_vectors
      s1_s2
  in
  let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 4)
  in
  let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 4)
  in
  let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) =
    Core.Slice.impl__copy_from_slice #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      s1_ntt
      (s1_s2.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = generate_key_pair_v44__COLUMNS_IN_A
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
  in
  let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          (s1_ntt <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        usize)
      (fun s1_ntt temp_1_ ->
          let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) =
            s1_ntt
          in
          let _:usize = temp_1_ in
          true)
      s1_ntt
      (fun s1_ntt i ->
          let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) =
            s1_ntt
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1_ntt
            i
            (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
                (s1_ntt.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4))
  in
  let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) =
    Libcrux_ml_dsa.Matrix.compute_as1_plus_s2 #v_SIMDUnit
      generate_key_pair_v44__ROWS_IN_A
      generate_key_pair_v44__COLUMNS_IN_A
      (a_as_ntt <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (s1_ntt <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (s1_s2 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      t0
  in
  let _:Prims.unit = () in
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 4)
  in
  let tmp0, tmp1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4)) =
    Libcrux_ml_dsa.Arithmetic.power2round_vector #v_SIMDUnit t0 t1
  in
  let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) = tmp0 in
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 4) = tmp1 in
  let _:Prims.unit = () in
  let verification_key:t_Slice u8 =
    Libcrux_ml_dsa.Encoding.Verification_key.generate_serialized #v_SIMDUnit
      seed_for_a
      (t1 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      verification_key
  in
  let signing_key:t_Slice u8 =
    Libcrux_ml_dsa.Encoding.Signing_key.generate_serialized #v_SIMDUnit #v_Shake256
      generate_key_pair_v44__ETA generate_key_pair_v44__ERROR_RING_ELEMENT_SIZE seed_for_a
      seed_for_signing verification_key
      (s1_s2 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (t0 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) signing_key
  in
  let hax_temp_output:Prims.unit = () in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)

let generate_key_pair_v65
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i8:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i9:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i10:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i11:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 signing_key <: usize) =.
            generate_key_pair_v65__SIGNING_KEY_SIZE
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 verification_key <: usize) =.
            generate_key_pair_v65__VERIFICATION_KEY_SIZE
            <:
            bool)
      in
      ()
  in
  let seed_expanded:t_Array u8 (sz 128) = Rust_primitives.Hax.repeat 0uy (sz 128) in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_init #v_Shake256Xof #FStar.Tactics.Typeclasses.solve ()
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      (randomness <: t_Slice u8)
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb_final #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      ((let list =
            [
              cast (generate_key_pair_v65__ROWS_IN_A <: usize) <: u8;
              cast (generate_key_pair_v65__COLUMNS_IN_A <: usize) <: u8
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice u8)
  in
  let tmp0, tmp1:(v_Shake256Xof & t_Array u8 (sz 128)) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      seed_expanded
  in
  let shake:v_Shake256Xof = tmp0 in
  let seed_expanded:t_Array u8 (sz 128) = tmp1 in
  let _:Prims.unit = () in
  let _:Prims.unit = () in
  let seed_for_a, seed_expanded:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (seed_expanded <: t_Slice u8)
      Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE
  in
  let seed_for_error_vectors, seed_for_signing:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      seed_expanded
      Libcrux_ml_dsa.Constants.v_SEED_FOR_ERROR_VECTORS_SIZE
  in
  let a_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 30) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 30)
  in
  let a_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 30) =
    Libcrux_ml_dsa.Samplex4.f_matrix_flat #v_Sampler
      #FStar.Tactics.Typeclasses.solve
      #v_SIMDUnit
      generate_key_pair_v65__COLUMNS_IN_A
      seed_for_a
      a_as_ntt
  in
  let s1_s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 11) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 11)
  in
  let s1_s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 11) =
    Libcrux_ml_dsa.Samplex4.sample_s1_and_s2 #v_SIMDUnit
      #v_Shake256X4
      generate_key_pair_v65__ETA
      seed_for_error_vectors
      s1_s2
  in
  let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 6) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 6)
  in
  let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 5) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 5)
  in
  let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 5) =
    Core.Slice.impl__copy_from_slice #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      s1_ntt
      (s1_s2.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = generate_key_pair_v65__COLUMNS_IN_A
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
  in
  let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 5) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          (s1_ntt <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        usize)
      (fun s1_ntt temp_1_ ->
          let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 5) =
            s1_ntt
          in
          let _:usize = temp_1_ in
          true)
      s1_ntt
      (fun s1_ntt i ->
          let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 5) =
            s1_ntt
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1_ntt
            i
            (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
                (s1_ntt.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 5))
  in
  let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 6) =
    Libcrux_ml_dsa.Matrix.compute_as1_plus_s2 #v_SIMDUnit
      generate_key_pair_v65__ROWS_IN_A
      generate_key_pair_v65__COLUMNS_IN_A
      (a_as_ntt <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (s1_ntt <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (s1_s2 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      t0
  in
  let _:Prims.unit = () in
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 6) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 6)
  in
  let tmp0, tmp1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 6) &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 6)) =
    Libcrux_ml_dsa.Arithmetic.power2round_vector #v_SIMDUnit t0 t1
  in
  let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 6) = tmp0 in
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 6) = tmp1 in
  let _:Prims.unit = () in
  let verification_key:t_Slice u8 =
    Libcrux_ml_dsa.Encoding.Verification_key.generate_serialized #v_SIMDUnit
      seed_for_a
      (t1 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      verification_key
  in
  let signing_key:t_Slice u8 =
    Libcrux_ml_dsa.Encoding.Signing_key.generate_serialized #v_SIMDUnit #v_Shake256
      generate_key_pair_v65__ETA generate_key_pair_v65__ERROR_RING_ELEMENT_SIZE seed_for_a
      seed_for_signing verification_key
      (s1_s2 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (t0 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) signing_key
  in
  let hax_temp_output:Prims.unit = () in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)

let generate_key_pair_v87
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i8:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i9:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i10:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i11:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 signing_key <: usize) =.
            generate_key_pair_v87__SIGNING_KEY_SIZE
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 verification_key <: usize) =.
            generate_key_pair_v87__VERIFICATION_KEY_SIZE
            <:
            bool)
      in
      ()
  in
  let seed_expanded:t_Array u8 (sz 128) = Rust_primitives.Hax.repeat 0uy (sz 128) in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_init #v_Shake256Xof #FStar.Tactics.Typeclasses.solve ()
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      (randomness <: t_Slice u8)
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb_final #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      ((let list =
            [
              cast (generate_key_pair_v87__ROWS_IN_A <: usize) <: u8;
              cast (generate_key_pair_v87__COLUMNS_IN_A <: usize) <: u8
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice u8)
  in
  let tmp0, tmp1:(v_Shake256Xof & t_Array u8 (sz 128)) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      seed_expanded
  in
  let shake:v_Shake256Xof = tmp0 in
  let seed_expanded:t_Array u8 (sz 128) = tmp1 in
  let _:Prims.unit = () in
  let _:Prims.unit = () in
  let seed_for_a, seed_expanded:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (seed_expanded <: t_Slice u8)
      Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE
  in
  let seed_for_error_vectors, seed_for_signing:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      seed_expanded
      Libcrux_ml_dsa.Constants.v_SEED_FOR_ERROR_VECTORS_SIZE
  in
  let a_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 56) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 56)
  in
  let a_as_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 56) =
    Libcrux_ml_dsa.Samplex4.f_matrix_flat #v_Sampler
      #FStar.Tactics.Typeclasses.solve
      #v_SIMDUnit
      generate_key_pair_v87__COLUMNS_IN_A
      seed_for_a
      a_as_ntt
  in
  let s1_s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 15) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 15)
  in
  let s1_s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 15) =
    Libcrux_ml_dsa.Samplex4.sample_s1_and_s2 #v_SIMDUnit
      #v_Shake256X4
      generate_key_pair_v87__ETA
      seed_for_error_vectors
      s1_s2
  in
  let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 8) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 8)
  in
  let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 7) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 7)
  in
  let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 7) =
    Core.Slice.impl__copy_from_slice #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      s1_ntt
      (s1_s2.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = generate_key_pair_v87__COLUMNS_IN_A
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
  in
  let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 7) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          (s1_ntt <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        usize)
      (fun s1_ntt temp_1_ ->
          let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 7) =
            s1_ntt
          in
          let _:usize = temp_1_ in
          true)
      s1_ntt
      (fun s1_ntt i ->
          let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 7) =
            s1_ntt
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1_ntt
            i
            (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
                (s1_ntt.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 7))
  in
  let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 8) =
    Libcrux_ml_dsa.Matrix.compute_as1_plus_s2 #v_SIMDUnit
      generate_key_pair_v87__ROWS_IN_A
      generate_key_pair_v87__COLUMNS_IN_A
      (a_as_ntt <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (s1_ntt <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (s1_s2 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      t0
  in
  let _:Prims.unit = () in
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 8) =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (sz 8)
  in
  let tmp0, tmp1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 8) &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 8)) =
    Libcrux_ml_dsa.Arithmetic.power2round_vector #v_SIMDUnit t0 t1
  in
  let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 8) = tmp0 in
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) (sz 8) = tmp1 in
  let _:Prims.unit = () in
  let verification_key:t_Slice u8 =
    Libcrux_ml_dsa.Encoding.Verification_key.generate_serialized #v_SIMDUnit
      seed_for_a
      (t1 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      verification_key
  in
  let signing_key:t_Slice u8 =
    Libcrux_ml_dsa.Encoding.Signing_key.generate_serialized #v_SIMDUnit #v_Shake256
      generate_key_pair_v87__ETA generate_key_pair_v87__ERROR_RING_ELEMENT_SIZE seed_for_a
      seed_for_signing verification_key
      (s1_s2 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (t0 <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) signing_key
  in
  let hax_temp_output:Prims.unit = () in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)
