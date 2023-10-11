module Hacspec_kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_KYBER768_SHARED_SECRET_SIZE: usize = Hacspec_kyber.Parameters.v_CPA_PKE_MESSAGE_SIZE

let v_KYBER768_KEY_GENERATION_SEED_SIZE: usize =
  Hacspec_kyber.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +! v_KYBER768_SHARED_SECRET_SIZE

let v_KYBER768_PUBLIC_KEY_SIZE: usize = Hacspec_kyber.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE

let v_KYBER768_SECRET_KEY_SIZE: usize =
  ((Hacspec_kyber.Parameters.v_CPA_PKE_SECRET_KEY_SIZE +!
      Hacspec_kyber.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE
      <:
      usize) +!
    Hacspec_kyber.Parameters.Hash_functions.v_H_DIGEST_SIZE
    <:
    usize) +!
  v_KYBER768_SHARED_SECRET_SIZE

let v_KYBER768_CIPHERTEXT_SIZE: usize = Hacspec_kyber.Parameters.v_CPA_PKE_CIPHERTEXT_SIZE

type t_BadRejectionSamplingRandomnessError =
  | BadRejectionSamplingRandomnessError : t_BadRejectionSamplingRandomnessError

type t_KeyPair = {
  f_pk:array u8 (sz 1184);
  f_sk:array u8 (sz 2400)
}

let impl__new (pk: array u8 (sz 1184)) (sk: array u8 (sz 2400)) : t_KeyPair =
  { f_pk = pk; f_sk = sk }

let generate_keypair (randomness: array u8 (sz 64))
    : Core.Result.t_Result t_KeyPair t_BadRejectionSamplingRandomnessError =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ind_cpa_keypair_randomness:slice u8 =
        randomness.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = Hacspec_kyber.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
          } ]
      in
      let implicit_rejection_value:slice u8 =
        randomness.[ {
            Core.Ops.Range.f_start = Hacspec_kyber.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
          } ]
      in
      let* ind_cpa_key_pair:Hacspec_kyber.Ind_cpa.t_KeyPair =
        match
          Core.Ops.Try_trait.f_branch (Hacspec_kyber.Ind_cpa.generate_keypair (Hacspec_lib.f_as_array
                    ind_cpa_keypair_randomness
                  <:
                  array u8 (sz 32))
              <:
              Core.Result.t_Result Hacspec_kyber.Ind_cpa.t_KeyPair
                t_BadRejectionSamplingRandomnessError)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist17:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_KeyPair t_BadRejectionSamplingRandomnessError)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist17)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let secret_key_serialized:array u8 (sz 2400) =
          Hacspec_kyber.Ind_cpa.impl__serialize_secret_key ind_cpa_key_pair
            (Hacspec_lib.f_as_array implicit_rejection_value <: array u8 (sz 32))
        in
        let key_pair:t_KeyPair =
          impl__new (Hacspec_kyber.Ind_cpa.impl__pk ind_cpa_key_pair <: array u8 (sz 1184))
            secret_key_serialized
        in
        Core.Result.Result_Ok key_pair))

let public_key_modulus_check (public_key: array u8 (sz 1184)) : bool =
  let encoded_ring_elements:slice u8 =
    public_key.[ {
        Core.Ops.Range.f_start = sz 0;
        Core.Ops.Range.f_end = v_KYBER768_PUBLIC_KEY_SIZE -! sz 32 <: usize
      } ]
  in
  let decoded_ring_elements:Hacspec_lib.Vector.t_Vector
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
    Hacspec_kyber.Serialize.vector_decode_12_ (Core.Result.impl__unwrap (Core.Convert.f_try_into encoded_ring_elements

            <:
            Core.Result.t_Result (array u8 (sz 1152))
              (Core.Convert.impl_6 (slice u8) (array u8 (sz 1152))).f_Error)
        <:
        array u8 (sz 1152))
  in
  encoded_ring_elements =.
  (Hacspec_kyber.Serialize.vector_encode_12_ decoded_ring_elements <: array u8 (sz 1152))

let encapsulate (public_key: array u8 (sz 1184)) (randomness: array u8 (sz 32))
    : Core.Result.t_Result (array u8 (sz 1088) & array u8 (sz 32))
      t_BadRejectionSamplingRandomnessError =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let _:Prims.unit =
        if ~.(public_key_modulus_check public_key <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: public_key_modulus_check(&public_key)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      let (to_hash: array u8 (sz 64)):array u8 (sz 64) =
        Hacspec_lib.f_push randomness
          (Rust_primitives.unsize (Hacspec_kyber.Parameters.Hash_functions.v_H (Rust_primitives.unsize
                      public_key
                    <:
                    slice u8)
                <:
                array u8 (sz 32))
            <:
            slice u8)
      in
      let hashed:array u8 (sz 64) =
        Hacspec_kyber.Parameters.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
      in
      let shared_secret, pseudorandomness:(slice u8 & slice u8) =
        Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: slice u8)
          v_KYBER768_SHARED_SECRET_SIZE
      in
      let* ciphertext:array u8 (sz 1088) =
        match
          Core.Ops.Try_trait.f_branch (Hacspec_kyber.Ind_cpa.encrypt public_key
                randomness
                (Hacspec_lib.f_as_array pseudorandomness <: array u8 (sz 32))
              <:
              Core.Result.t_Result (array u8 (sz 1088)) t_BadRejectionSamplingRandomnessError)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist18:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (array u8 (sz 1088) & array u8 (sz 32))
                  t_BadRejectionSamplingRandomnessError)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist18)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok (ciphertext, Hacspec_lib.f_as_array shared_secret)))

let decapsulate (ciphertext: array u8 (sz 1088)) (secret_key: array u8 (sz 2400)) : array u8 (sz 32) =
  let ind_cpa_secret_key, secret_key:(slice u8 & slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize secret_key <: slice u8)
      Hacspec_kyber.Parameters.v_CPA_PKE_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(slice u8 & slice u8) =
    Core.Slice.impl__split_at secret_key Hacspec_kyber.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(slice u8 & slice u8) =
    Core.Slice.impl__split_at secret_key Hacspec_kyber.Parameters.Hash_functions.v_H_DIGEST_SIZE
  in
  let decrypted:array u8 (sz 32) =
    Hacspec_kyber.Ind_cpa.decrypt (Hacspec_lib.f_as_array ind_cpa_secret_key <: array u8 (sz 1152))
      ciphertext
  in
  let (to_hash: array u8 (sz 64)):array u8 (sz 64) =
    Hacspec_lib.f_push decrypted ind_cpa_public_key_hash
  in
  let hashed:array u8 (sz 64) =
    Hacspec_kyber.Parameters.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
  in
  let success_shared_secret, pseudorandomness:(slice u8 & slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: slice u8)
      v_KYBER768_SHARED_SECRET_SIZE
  in
  let (to_hash: array u8 (sz 1120)):array u8 (sz 1120) =
    Hacspec_lib.f_push implicit_rejection_value (Rust_primitives.unsize ciphertext <: slice u8)
  in
  let (rejection_shared_secret: array u8 (sz 32)):array u8 (sz 32) =
    Hacspec_kyber.Parameters.Hash_functions.v_J (Rust_primitives.unsize to_hash <: slice u8)
  in
  let reencrypted_ciphertext:Core.Result.t_Result (array u8 (sz 1088))
    t_BadRejectionSamplingRandomnessError =
    Hacspec_kyber.Ind_cpa.encrypt (Hacspec_lib.f_as_array ind_cpa_public_key <: array u8 (sz 1184))
      decrypted
      (Hacspec_lib.f_as_array pseudorandomness <: array u8 (sz 32))
  in
  match reencrypted_ciphertext with
  | Core.Result.Result_Ok reencrypted ->
    if ciphertext =. reencrypted
    then Hacspec_lib.f_as_array success_shared_secret
    else rejection_shared_secret
  | _ -> rejection_shared_secret