module Hacspec_kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_KYBER768_SHARED_SECRET_SIZE: usize = Hacspec_kyber.Parameters.v_CPA_PKE_MESSAGE_SIZE

let v_KYBER768_KEY_GENERATION_SEED_SIZE: usize =
  Hacspec_kyber.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +. v_KYBER768_SHARED_SECRET_SIZE

let v_KYBER768_PUBLIC_KEY_SIZE: usize = Hacspec_kyber.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE

let v_KYBER768_SECRET_KEY_SIZE: usize =
  ((Hacspec_kyber.Parameters.v_CPA_PKE_SECRET_KEY_SIZE +.
      Hacspec_kyber.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE
      <:
      usize) +.
    Hacspec_kyber.Parameters.Hash_functions.v_H_DIGEST_SIZE
    <:
    usize) +.
  v_KYBER768_SHARED_SECRET_SIZE

let v_KYBER768_CIPHERTEXT_SIZE: usize = Hacspec_kyber.Parameters.v_CPA_PKE_CIPHERTEXT_SIZE

let t_PublicKey = array u8 1184sz

let t_PrivateKey = array u8 2400sz

let t_Ciphertext = array u8 1088sz

let t_SharedSecret = array u8 32sz

type t_BadRejectionSamplingRandomnessError =
  | BadRejectionSamplingRandomnessError : t_BadRejectionSamplingRandomnessError

type t_KeyPair = {
  f_pk:array u8 1184sz;
  f_sk:array u8 2400sz
}

let new_under_impl (pk: array u8 1184sz) (sk: array u8 2400sz) : t_KeyPair =
  { Hacspec_kyber.KeyPair.f_pk = pk; Hacspec_kyber.KeyPair.f_sk = sk }

let pk_under_impl (self: t_KeyPair) : array u8 1184sz = self.Hacspec_kyber.KeyPair.f_pk

let sk_under_impl (self: t_KeyPair) : array u8 2400sz = self.Hacspec_kyber.KeyPair.f_sk

let generate_keypair (randomness: array u8 64sz)
    : Core.Result.t_Result t_KeyPair t_BadRejectionSamplingRandomnessError =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ind_cpa_keypair_randomness:slice u8 =
        randomness.[ {
            Core.Ops.Range.Range.f_start = 0sz;
            Core.Ops.Range.Range.f_end = Hacspec_kyber.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
          } ]
      in
      let implicit_rejection_value:slice u8 =
        randomness.[ {
            Core.Ops.Range.RangeFrom.f_start
            =
            Hacspec_kyber.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
          } ]
      in
      let* ind_cpa_key_pair:Hacspec_kyber.Ind_cpa.t_KeyPair =
        match
          Core.Ops.Try_trait.Try.branch (Hacspec_kyber.Ind_cpa.generate_keypair (Hacspec_lib.ArrayConversion.as_array
                    ind_cpa_keypair_randomness
                  <:
                  array u8 32sz)
              <:
              Core.Result.t_Result Hacspec_kyber.Ind_cpa.t_KeyPair
                t_BadRejectionSamplingRandomnessError)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist17:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                  residual
                <:
                Core.Result.t_Result t_KeyPair t_BadRejectionSamplingRandomnessError)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist17)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let secret_key_serialized:array u8 2400sz =
          Hacspec_kyber.Ind_cpa.serialize_secret_key_under_impl ind_cpa_key_pair
            (Hacspec_lib.ArrayConversion.as_array implicit_rejection_value <: array u8 32sz)
        in
        let key_pair:t_KeyPair =
          new_under_impl (Hacspec_kyber.Ind_cpa.pk_under_impl ind_cpa_key_pair <: array u8 1184sz)
            secret_key_serialized
        in
        Core.Result.Result_Ok key_pair))

let public_key_modulus_check (public_key: array u8 1184sz) : bool =
  let encoded_ring_elements:slice u8 =
    public_key.[ {
        Core.Ops.Range.Range.f_start = 0sz;
        Core.Ops.Range.Range.f_end = v_KYBER768_PUBLIC_KEY_SIZE -. 32sz <: usize
      } ]
  in
  let decoded_ring_elements:Hacspec_lib.Vector.t_Vector
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Hacspec_kyber.Serialize.vector_decode_12_ (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into
              encoded_ring_elements
            <:
            Core.Result.t_Result (array u8 1152sz) _)
        <:
        array u8 1152sz)
  in
  encoded_ring_elements =.
  (Hacspec_kyber.Serialize.vector_encode_12_ decoded_ring_elements <: array u8 1152sz)

let encapsulate (public_key: array u8 1184sz) (randomness: array u8 32sz)
    : Core.Result.t_Result (array u8 1088sz & array u8 32sz) t_BadRejectionSamplingRandomnessError =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let _:Prims.unit =
        if ~.(public_key_modulus_check public_key <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: public_key_modulus_check(&public_key)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      let (to_hash: array u8 64sz):array u8 64sz =
        Hacspec_lib.UpdatingArray2.push randomness
          (Rust_primitives.unsize (Hacspec_kyber.Parameters.Hash_functions.v_H (Rust_primitives.unsize
                      public_key
                    <:
                    slice u8)
                <:
                array u8 32sz)
            <:
            slice u8)
      in
      let hashed:array u8 64sz =
        Hacspec_kyber.Parameters.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
      in
      let shared_secret, pseudorandomness:(slice u8 & slice u8) =
        Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8)
          v_KYBER768_SHARED_SECRET_SIZE
      in
      let* ciphertext:array u8 1088sz =
        match
          Core.Ops.Try_trait.Try.branch (Hacspec_kyber.Ind_cpa.encrypt public_key
                randomness
                (Hacspec_lib.ArrayConversion.as_array pseudorandomness <: array u8 32sz)
              <:
              Core.Result.t_Result (array u8 1088sz) t_BadRejectionSamplingRandomnessError)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist18:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                  residual
                <:
                Core.Result.t_Result (array u8 1088sz & array u8 32sz)
                  t_BadRejectionSamplingRandomnessError)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist18)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok (ciphertext, Hacspec_lib.ArrayConversion.as_array shared_secret)))

let decapsulate (ciphertext: array u8 1088sz) (secret_key: array u8 2400sz) : array u8 32sz =
  let ind_cpa_secret_key, secret_key:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize secret_key <: slice u8)
      Hacspec_kyber.Parameters.v_CPA_PKE_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl secret_key Hacspec_kyber.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl secret_key
      Hacspec_kyber.Parameters.Hash_functions.v_H_DIGEST_SIZE
  in
  let decrypted:array u8 32sz =
    Hacspec_kyber.Ind_cpa.decrypt (Hacspec_lib.ArrayConversion.as_array ind_cpa_secret_key
        <:
        array u8 1152sz)
      ciphertext
  in
  let (to_hash: array u8 64sz):array u8 64sz =
    Hacspec_lib.UpdatingArray2.push decrypted ind_cpa_public_key_hash
  in
  let hashed:array u8 64sz =
    Hacspec_kyber.Parameters.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
  in
  let success_shared_secret, pseudorandomness:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8)
      v_KYBER768_SHARED_SECRET_SIZE
  in
  let (to_hash: array u8 1120sz):array u8 1120sz =
    Hacspec_lib.UpdatingArray2.push implicit_rejection_value
      (Rust_primitives.unsize ciphertext <: slice u8)
  in
  let (rejection_shared_secret: array u8 32sz):array u8 32sz =
    Hacspec_kyber.Parameters.Hash_functions.v_J (Rust_primitives.unsize to_hash <: slice u8)
  in
  let reencrypted_ciphertext:Core.Result.t_Result (array u8 1088sz)
    t_BadRejectionSamplingRandomnessError =
    Hacspec_kyber.Ind_cpa.encrypt (Hacspec_lib.ArrayConversion.as_array ind_cpa_public_key
        <:
        array u8 1184sz)
      decrypted
      (Hacspec_lib.ArrayConversion.as_array pseudorandomness <: array u8 32sz)
  in
  match reencrypted_ciphertext with
  | Core.Result.Result_Ok reencrypted ->
    if ciphertext =. reencrypted
    then Hacspec_lib.ArrayConversion.as_array success_shared_secret
    else rejection_shared_secret
  | _ -> rejection_shared_secret