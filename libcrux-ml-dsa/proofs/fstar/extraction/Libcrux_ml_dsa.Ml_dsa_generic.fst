module Libcrux_ml_dsa.Ml_dsa_generic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  let open Libcrux_sha3.Portable.Incremental in
  ()

let t_SigningError_cast_to_repr (x: t_SigningError) =
  match x with | SigningError_RejectionSamplingError  -> isz 0

let t_VerificationError_cast_to_repr (x: t_VerificationError) =
  match x with
  | VerificationError_MalformedHintError  -> isz 0
  | VerificationError_SignerResponseExceedsBoundError  -> isz 1
  | VerificationError_CommitmentHashesDontMatchError  -> isz 3

let generate_key_pair
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256 #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_VERIFICATION_KEY_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i7:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (randomness: t_Array u8 (sz 32))
     =
  let seed_expanded:t_Array u8 (sz 128) = Rust_primitives.Hax.repeat 0uy (sz 128) in
  let seed_expanded:t_Array u8 (sz 128) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256 #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      (sz 128)
      (randomness <: t_Slice u8)
      seed_expanded
  in
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
  let a_as_ntt:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Libcrux_ml_dsa.Samplex4.matrix_A #v_SIMDUnit
      #v_Shake128X4
      v_ROWS_IN_A
      v_COLUMNS_IN_A
      (Libcrux_ml_dsa.Utils.into_padded_array (sz 34) seed_for_a <: t_Array u8 (sz 34))
  in
  let s1, s2:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
    Libcrux_ml_dsa.Samplex4.sample_s1_and_s2 #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      v_COLUMNS_IN_A
      v_ROWS_IN_A
      (Libcrux_ml_dsa.Utils.into_padded_array (sz 66) seed_for_error_vectors <: t_Array u8 (sz 66))
  in
  let t:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Libcrux_ml_dsa.Matrix.compute_As1_plus_s2 #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A a_as_ntt s1 s2
  in
  let t0, t1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
    Libcrux_ml_dsa.Arithmetic.power2round_vector #v_SIMDUnit v_ROWS_IN_A t
  in
  let verification_key_serialized:t_Array u8 v_VERIFICATION_KEY_SIZE =
    Libcrux_ml_dsa.Encoding.Verification_key.generate_serialized #v_SIMDUnit
      v_ROWS_IN_A
      v_VERIFICATION_KEY_SIZE
      seed_for_a
      t1
  in
  let signing_key_serialized:t_Array u8 v_SIGNING_KEY_SIZE =
    Libcrux_ml_dsa.Encoding.Signing_key.generate_serialized #v_SIMDUnit #v_Shake256 v_ROWS_IN_A
      v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE seed_for_a seed_for_signing
      (verification_key_serialized <: t_Slice u8) s1 s2 t0
  in
  signing_key_serialized, verification_key_serialized
  <:
  (t_Array u8 v_SIGNING_KEY_SIZE & t_Array u8 v_VERIFICATION_KEY_SIZE)

let sign
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256 #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT: usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i7:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  let seed_for_A, seed_for_signing, verification_key_hash, s1_as_ntt, s2_as_ntt, t0_as_ntt:(t_Array
      u8 (sz 32) &
    t_Array u8 (sz 32) &
    t_Array u8 (sz 64) &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
    Libcrux_ml_dsa.Encoding.Signing_key.deserialize_then_ntt #v_SIMDUnit
      v_ROWS_IN_A
      v_COLUMNS_IN_A
      v_ETA
      v_ERROR_RING_ELEMENT_SIZE
      v_SIGNING_KEY_SIZE
      signing_key
  in
  let v_A_as_ntt:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Libcrux_ml_dsa.Samplex4.matrix_A #v_SIMDUnit
      #v_Shake128X4
      v_ROWS_IN_A
      v_COLUMNS_IN_A
      (Libcrux_ml_dsa.Utils.into_padded_array (sz 34) (seed_for_A <: t_Slice u8)
        <:
        t_Array u8 (sz 34))
  in
  let message_representative:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_new #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      (verification_key_hash <: t_Slice u8)
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze =
    Libcrux_sha3.Portable.Incremental.f_absorb_final #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      message
  in
  let tmp0, tmp1:(Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze & t_Array u8 (sz 64)) =
    Libcrux_sha3.Portable.Incremental.f_squeeze #Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      message_representative
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze = tmp0 in
  let message_representative:t_Array u8 (sz 64) = tmp1 in
  let _:Prims.unit = () in
  let _:Prims.unit = () in
  let mask_seed:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_new #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      (seed_for_signing <: t_Slice u8)
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      (randomness <: t_Slice u8)
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze =
    Libcrux_sha3.Portable.Incremental.f_absorb_final #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      (message_representative <: t_Slice u8)
  in
  let tmp0, tmp1:(Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze & t_Array u8 (sz 64)) =
    Libcrux_sha3.Portable.Incremental.f_squeeze #Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      mask_seed
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze = tmp0 in
  let mask_seed:t_Array u8 (sz 64) = tmp1 in
  let _:Prims.unit = () in
  let _:Prims.unit = () in
  let (domain_separator_for_mask: u16):u16 = 0us in
  let v_BETA:i32 = cast (v_ONES_IN_VERIFIER_CHALLENGE *! v_ETA <: usize) <: i32 in
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
          attempt <. Libcrux_ml_dsa.Constants.v_REJECTION_SAMPLE_BOUND <: bool)
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
          let tmp0, out:(u16 &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A) =
            Libcrux_ml_dsa.Sample.sample_mask_vector #v_SIMDUnit
              #v_Shake256
              #v_Shake256X4
              v_COLUMNS_IN_A
              v_GAMMA1_EXPONENT
              (Libcrux_ml_dsa.Utils.into_padded_array (sz 66) (mask_seed <: t_Slice u8)
                <:
                t_Array u8 (sz 66))
              domain_separator_for_mask
          in
          let domain_separator_for_mask:u16 = tmp0 in
          let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_COLUMNS_IN_A =
            out
          in
          let v_A_times_mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Libcrux_ml_dsa.Matrix.compute_A_times_mask #v_SIMDUnit
              v_ROWS_IN_A
              v_COLUMNS_IN_A
              v_A_as_ntt
              mask
          in
          let w0, commitment:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              v_ROWS_IN_A &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
            Libcrux_ml_dsa.Arithmetic.decompose_vector #v_SIMDUnit
              v_ROWS_IN_A
              v_GAMMA2
              v_A_times_mask
          in
          let commitment_hash_candidate:t_Array u8 v_COMMITMENT_HASH_SIZE =
            Rust_primitives.Hax.repeat 0uy v_COMMITMENT_HASH_SIZE
          in
          let commitment_serialized:t_Array u8 v_COMMITMENT_VECTOR_SIZE =
            Libcrux_ml_dsa.Encoding.Commitment.serialize_vector #v_SIMDUnit
              v_ROWS_IN_A
              v_COMMITMENT_RING_ELEMENT_SIZE
              v_COMMITMENT_VECTOR_SIZE
              commitment
          in
          let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
            Libcrux_sha3.Portable.Incremental.f_new #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
              #(sz 136)
              #FStar.Tactics.Typeclasses.solve
              ()
          in
          let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
            Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
              #(sz 136)
              #FStar.Tactics.Typeclasses.solve
              shake
              (message_representative <: t_Slice u8)
          in
          let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze =
            Libcrux_sha3.Portable.Incremental.f_absorb_final #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
              #(sz 136)
              #FStar.Tactics.Typeclasses.solve
              shake
              (commitment_serialized <: t_Slice u8)
          in
          let tmp0, tmp1:(Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze &
            t_Array u8 v_COMMITMENT_HASH_SIZE) =
            Libcrux_sha3.Portable.Incremental.f_squeeze #Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze
              #(sz 136)
              #FStar.Tactics.Typeclasses.solve
              shake
              commitment_hash_candidate
          in
          let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze = tmp0 in
          let commitment_hash_candidate:t_Array u8 v_COMMITMENT_HASH_SIZE = tmp1 in
          let _:Prims.unit = () in
          let _:Prims.unit = () in
          let verifier_challenge_as_ntt:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
          =
            Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
              (Libcrux_ml_dsa.Sample.sample_challenge_ring_element #v_SIMDUnit
                  #v_Shake256
                  v_ONES_IN_VERIFIER_CHALLENGE
                  (Core.Result.impl__unwrap #(t_Array u8 (sz 32))
                      #Core.Array.t_TryFromSliceError
                      (Core.Convert.f_try_into #(t_Slice u8)
                          #(t_Array u8 (sz 32))
                          #FStar.Tactics.Typeclasses.solve
                          (commitment_hash_candidate.[ {
                                Core.Ops.Range.f_start = sz 0;
                                Core.Ops.Range.f_end
                                =
                                Libcrux_ml_dsa.Constants.v_VERIFIER_CHALLENGE_SEED_SIZE
                              }
                              <:
                              Core.Ops.Range.t_Range usize ]
                            <:
                            t_Slice u8)
                        <:
                        Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError)
                    <:
                    t_Array u8 (sz 32))
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let challenge_times_s1:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
            Libcrux_ml_dsa.Matrix.vector_times_ring_element #v_SIMDUnit
              v_COLUMNS_IN_A
              s1_as_ntt
              verifier_challenge_as_ntt
          in
          let challenge_times_s2:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
            Libcrux_ml_dsa.Matrix.vector_times_ring_element #v_SIMDUnit
              v_ROWS_IN_A
              s2_as_ntt
              verifier_challenge_as_ntt
          in
          let signer_response_candidate:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
            Libcrux_ml_dsa.Matrix.add_vectors #v_SIMDUnit v_COLUMNS_IN_A mask challenge_times_s1
          in
          let w0_minus_challenge_times_s2:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
            Libcrux_ml_dsa.Matrix.subtract_vectors #v_SIMDUnit v_ROWS_IN_A w0 challenge_times_s2
          in
          if
            Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
              v_COLUMNS_IN_A
              signer_response_candidate
              ((1l <<! v_GAMMA1_EXPONENT <: i32) -! v_BETA <: i32)
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
                v_ROWS_IN_A
                w0_minus_challenge_times_s2
                (v_GAMMA2 -! v_BETA <: i32)
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
                Libcrux_ml_dsa.Matrix.vector_times_ring_element #v_SIMDUnit
                  v_ROWS_IN_A
                  t0_as_ntt
                  verifier_challenge_as_ntt
              in
              if
                Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
                  v_ROWS_IN_A
                  challenge_times_t0
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
                let w0_minus_c_times_s2_plus_c_times_t0:t_Array
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
                  Libcrux_ml_dsa.Matrix.add_vectors #v_SIMDUnit
                    v_ROWS_IN_A
                    w0_minus_challenge_times_s2
                    challenge_times_t0
                in
                let hint_candidate, ones_in_hint:(t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize
                ) =
                  Libcrux_ml_dsa.Arithmetic.make_hint #v_SIMDUnit
                    v_ROWS_IN_A
                    v_GAMMA2
                    w0_minus_c_times_s2_plus_c_times_t0
                    commitment
                in
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
                  let attempt:usize = Libcrux_ml_dsa.Constants.v_REJECTION_SAMPLE_BOUND in
                  let commitment_hash:Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) =
                    Core.Option.Option_Some commitment_hash_candidate
                    <:
                    Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE)
                  in
                  let signer_response:Core.Option.t_Option
                  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                      v_COLUMNS_IN_A) =
                    Core.Option.Option_Some signer_response_candidate
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
  match
    match commitment_hash with
    | Core.Option.Option_Some commitment_hash ->
      Core.Result.Result_Ok commitment_hash
      <:
      Core.Result.t_Result (t_Array u8 v_COMMITMENT_HASH_SIZE) t_SigningError
    | Core.Option.Option_None  ->
      Core.Result.Result_Err (SigningError_RejectionSamplingError <: t_SigningError)
      <:
      Core.Result.t_Result (t_Array u8 v_COMMITMENT_HASH_SIZE) t_SigningError
  with
  | Core.Result.Result_Ok commitment_hash ->
    (match
        match signer_response with
        | Core.Option.Option_Some signer_response ->
          Core.Result.Result_Ok signer_response
          <:
          Core.Result.t_Result
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
            t_SigningError
        | Core.Option.Option_None  ->
          Core.Result.Result_Err (SigningError_RejectionSamplingError <: t_SigningError)
          <:
          Core.Result.t_Result
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
            t_SigningError
      with
      | Core.Result.Result_Ok signer_response ->
        (match
            match hint with
            | Core.Option.Option_Some hint ->
              Core.Result.Result_Ok hint
              <:
              Core.Result.t_Result (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) t_SigningError
            | Core.Option.Option_None  ->
              Core.Result.Result_Err (SigningError_RejectionSamplingError <: t_SigningError)
              <:
              Core.Result.t_Result (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) t_SigningError
          with
          | Core.Result.Result_Ok hint ->
            let signature:t_Array u8 v_SIGNATURE_SIZE =
              Libcrux_ml_dsa.Encoding.Signature.impl__serialize #v_SIMDUnit
                v_COMMITMENT_HASH_SIZE
                v_COLUMNS_IN_A
                v_ROWS_IN_A
                v_GAMMA1_EXPONENT
                v_GAMMA1_RING_ELEMENT_SIZE
                v_MAX_ONES_IN_HINT
                v_SIGNATURE_SIZE
                ({
                    f_commitment_hash = commitment_hash;
                    f_signer_response = signer_response;
                    f_hint = hint
                  }
                  <:
                  t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A)
            in
            Core.Result.Result_Ok
            (Libcrux_ml_dsa.Types.MLDSASignature signature
              <:
              Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
            <:
            Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
              t_SigningError
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
              t_SigningError)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE) t_SigningError
    )
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE) t_SigningError

let verify
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message: t_Slice u8)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
     =
  let seed_for_A, t1:(t_Array u8 (sz 32) &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
    Libcrux_ml_dsa.Encoding.Verification_key.deserialize #v_SIMDUnit
      v_ROWS_IN_A
      v_VERIFICATION_KEY_SIZE
      verification_key_serialized
  in
  match
    Libcrux_ml_dsa.Encoding.Signature.impl__deserialize #v_SIMDUnit
      v_COMMITMENT_HASH_SIZE
      v_COLUMNS_IN_A
      v_ROWS_IN_A
      v_GAMMA1_EXPONENT
      v_GAMMA1_RING_ELEMENT_SIZE
      v_MAX_ONES_IN_HINT
      v_SIGNATURE_SIZE
      signature_serialized
  with
  | Core.Result.Result_Ok signature ->
    if
      ~.(Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
          v_COLUMNS_IN_A
          signature.f_signer_response
          ((2l <<! v_GAMMA1_EXPONENT <: i32) -! v_BETA <: i32)
        <:
        bool)
    then
      let v_A_as_ntt:t_Array
        (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
        v_ROWS_IN_A =
        Libcrux_ml_dsa.Samplex4.matrix_A #v_SIMDUnit
          #v_Shake128X4
          v_ROWS_IN_A
          v_COLUMNS_IN_A
          (Libcrux_ml_dsa.Utils.into_padded_array (sz 34) (seed_for_A <: t_Slice u8)
            <:
            t_Array u8 (sz 34))
      in
      let verification_key_hash:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
      let verification_key_hash:t_Array u8 (sz 64) =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256 #v_Shake256
          #FStar.Tactics.Typeclasses.solve
          (sz 64)
          (verification_key_serialized <: t_Slice u8)
          verification_key_hash
      in
      let message_representative:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
        Libcrux_sha3.Portable.Incremental.f_new #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          ()
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
        Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          (verification_key_hash <: t_Slice u8)
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze =
        Libcrux_sha3.Portable.Incremental.f_absorb_final #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          message
      in
      let tmp0, tmp1:(Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze & t_Array u8 (sz 64)) =
        Libcrux_sha3.Portable.Incremental.f_squeeze #Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          message_representative
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze = tmp0 in
      let message_representative:t_Array u8 (sz 64) = tmp1 in
      let _:Prims.unit = () in
      let _:Prims.unit = () in
      let verifier_challenge_as_ntt:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
        Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
          (Libcrux_ml_dsa.Sample.sample_challenge_ring_element #v_SIMDUnit
              #v_Shake256
              v_ONES_IN_VERIFIER_CHALLENGE
              (Core.Result.impl__unwrap #(t_Array u8 (sz 32))
                  #Core.Array.t_TryFromSliceError
                  (Core.Convert.f_try_into #(t_Slice u8)
                      #(t_Array u8 (sz 32))
                      #FStar.Tactics.Typeclasses.solve
                      (signature.f_commitment_hash.[ {
                            Core.Ops.Range.f_start = sz 0;
                            Core.Ops.Range.f_end
                            =
                            Libcrux_ml_dsa.Constants.v_VERIFIER_CHALLENGE_SEED_SIZE
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                    <:
                    Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError)
                <:
                t_Array u8 (sz 32))
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let w_approx:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
        v_ROWS_IN_A =
        Libcrux_ml_dsa.Matrix.compute_w_approx #v_SIMDUnit
          v_ROWS_IN_A
          v_COLUMNS_IN_A
          v_A_as_ntt
          signature.f_signer_response
          verifier_challenge_as_ntt
          t1
      in
      let commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE =
        Rust_primitives.Hax.repeat 0uy v_COMMITMENT_HASH_SIZE
      in
      let commitment:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
        v_ROWS_IN_A =
        Libcrux_ml_dsa.Arithmetic.use_hint #v_SIMDUnit
          v_ROWS_IN_A
          v_GAMMA2
          signature.f_hint
          w_approx
      in
      let commitment_serialized:t_Array u8 v_COMMITMENT_VECTOR_SIZE =
        Libcrux_ml_dsa.Encoding.Commitment.serialize_vector #v_SIMDUnit
          v_ROWS_IN_A
          v_COMMITMENT_RING_ELEMENT_SIZE
          v_COMMITMENT_VECTOR_SIZE
          commitment
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
        Libcrux_sha3.Portable.Incremental.f_new #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          ()
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
        Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          (message_representative <: t_Slice u8)
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze =
        Libcrux_sha3.Portable.Incremental.f_absorb_final #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          (commitment_serialized <: t_Slice u8)
      in
      let tmp0, tmp1:(Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze &
        t_Array u8 v_COMMITMENT_HASH_SIZE) =
        Libcrux_sha3.Portable.Incremental.f_squeeze #Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          commitment_hash
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze = tmp0 in
      let commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE = tmp1 in
      let _:Prims.unit = () in
      let _:Prims.unit = () in
      if signature.f_commitment_hash <>. commitment_hash
      then
        Core.Result.Result_Err
        (VerificationError_CommitmentHashesDontMatchError <: t_VerificationError)
        <:
        Core.Result.t_Result Prims.unit t_VerificationError
      else
        Core.Result.Result_Ok (() <: Prims.unit)
        <:
        Core.Result.t_Result Prims.unit t_VerificationError
    else
      Core.Result.Result_Err
      (VerificationError_SignerResponseExceedsBoundError <: t_VerificationError)
      <:
      Core.Result.t_Result Prims.unit t_VerificationError
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit t_VerificationError
