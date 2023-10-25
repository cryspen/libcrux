module Libcrux.Kem.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_KyberCiphertext (#v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

let impl (#v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberCiphertext v_SIZE) (t_Slice u8) =
  {
    f_as_ref
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_1 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberCiphertext v_SIZE) (t_Array u8 v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = value } }

let impl_2 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberCiphertext v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from
    =
    fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = Core.Clone.f_clone value }
  }

let impl_3 (#v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_KyberCiphertext v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_KyberCiphertext v_SIZE) -> value.f_value }

let impl_4 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberCiphertext v_SIZE) (t_Slice u8) =
  {
    f_Error = Core.Array.t_TryFromSliceError;
    f_try_from
    =
    fun (#v_SIZE: usize) (value: t_Slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist6:t_Array u8 v_SIZE =
            match
              Core.Ops.Try_trait.f_branch (Core.Convert.f_try_into value
                  <:
                  Core.Result.t_Result (t_Array u8 v_SIZE) Core.Array.t_TryFromSliceError)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist5:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (t_KyberCiphertext v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist5)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist7:t_KyberCiphertext v_SIZE = { f_value = hoist6 } in
            Core.Result.Result_Ok hoist7))
  }

let impl_5 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) usize =
  {
    f_Output = u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_6 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_7 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_8 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun
      (#v_SIZE: usize)
      (self: t_KyberCiphertext v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.f_value.[ range ]
  }

let impl_9__as_slice (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

let impl_9__split_at (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (mid: usize)
    : (t_Slice u8 & t_Slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: t_Slice u8) mid

let impl_9__len (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) : usize = v_SIZE

type t_KyberPrivateKey (#v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

let impl_10 (#v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberPrivateKey v_SIZE) (t_Slice u8) =
  {
    f_as_ref
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_11 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = value } }

let impl_12 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from
    =
    fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = Core.Clone.f_clone value }
  }

let impl_13 (#v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_KyberPrivateKey v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_KyberPrivateKey v_SIZE) -> value.f_value }

let impl_14 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberPrivateKey v_SIZE) (t_Slice u8) =
  {
    f_Error = Core.Array.t_TryFromSliceError;
    f_try_from
    =
    fun (#v_SIZE: usize) (value: t_Slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist9:t_Array u8 v_SIZE =
            match
              Core.Ops.Try_trait.f_branch (Core.Convert.f_try_into value
                  <:
                  Core.Result.t_Result (t_Array u8 v_SIZE) Core.Array.t_TryFromSliceError)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist8:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (t_KyberPrivateKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist8)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist10:t_KyberPrivateKey v_SIZE = { f_value = hoist9 } in
            Core.Result.Result_Ok hoist10))
  }

let impl_15 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) usize =
  {
    f_Output = u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_16 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_17 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_18 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun
      (#v_SIZE: usize)
      (self: t_KyberPrivateKey v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.f_value.[ range ]
  }

let impl_19__as_slice (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

let impl_19__split_at (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (mid: usize)
    : (t_Slice u8 & t_Slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: t_Slice u8) mid

let impl_19__len (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) : usize = v_SIZE

type t_KyberPublicKey (#v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

let impl_20 (#v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberPublicKey v_SIZE) (t_Slice u8) =
  {
    f_as_ref
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_21 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberPublicKey v_SIZE) (t_Array u8 v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = value } }

let impl_22 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberPublicKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from
    =
    fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = Core.Clone.f_clone value }
  }

let impl_23 (#v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_KyberPublicKey v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_KyberPublicKey v_SIZE) -> value.f_value }

let impl_24 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberPublicKey v_SIZE) (t_Slice u8) =
  {
    f_Error = Core.Array.t_TryFromSliceError;
    f_try_from
    =
    fun (#v_SIZE: usize) (value: t_Slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist12:t_Array u8 v_SIZE =
            match
              Core.Ops.Try_trait.f_branch (Core.Convert.f_try_into value
                  <:
                  Core.Result.t_Result (t_Array u8 v_SIZE) Core.Array.t_TryFromSliceError)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist11:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (t_KyberPublicKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist11)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist13:t_KyberPublicKey v_SIZE = { f_value = hoist12 } in
            Core.Result.Result_Ok hoist13))
  }

let impl_25 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) usize =
  {
    f_Output = u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_26 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_27 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_28 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun
      (#v_SIZE: usize)
      (self: t_KyberPublicKey v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.f_value.[ range ]
  }

let impl_29__as_slice (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

let impl_29__split_at (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (mid: usize)
    : (t_Slice u8 & t_Slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: t_Slice u8) mid

let impl_29__len (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) : usize = v_SIZE

type t_KyberKeyPair (#v_PRIVATE_KEY_SIZE: usize) (#v_PUBLIC_KEY_SIZE: usize) = {
  f_sk:t_KyberPrivateKey v_PRIVATE_KEY_SIZE;
  f_pk:t_KyberPublicKey v_PUBLIC_KEY_SIZE
}

type t_BadRejectionSamplingRandomnessError =
  | BadRejectionSamplingRandomnessError : t_BadRejectionSamplingRandomnessError

let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +!
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

let generate_keypair
      (#v_K #v_CPA_PRIVATE_KEY_SIZE #v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE #v_BYTES_PER_RING_ELEMENT #v_ETA1 #v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
    : Core.Result.t_Result (t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      t_BadRejectionSamplingRandomnessError =
  let ind_cpa_keypair_randomness:t_Slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = sz 0;
        Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      } ]
  in
  let implicit_rejection_value:t_Slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      } ]
  in
  let (ind_cpa_private_key, public_key), sampling_a_error:((Libcrux.Kem.Kyber.Ind_cpa.t_PrivateKey
      v_CPA_PRIVATE_KEY_SIZE &
      t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber.Ind_cpa.generate_keypair ind_cpa_keypair_randomness
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.serialize_secret_key (Rust_primitives.unsize (Libcrux.Kem.Kyber.Ind_cpa.impl_9__as_slice
              ind_cpa_private_key
            <:
            t_Array u8 v_CPA_PRIVATE_KEY_SIZE)
        <:
        t_Slice u8)
      (Rust_primitives.unsize (impl_29__as_slice public_key <: t_Array u8 v_PUBLIC_KEY_SIZE)
        <:
        t_Slice u8)
      implicit_rejection_value
  in
  match sampling_a_error with
  | Core.Option.Option_Some error -> Core.Result.Result_Err error
  | _ ->
    let (private_key: t_KyberPrivateKey v_PRIVATE_KEY_SIZE):t_KyberPrivateKey v_PRIVATE_KEY_SIZE =
      Core.Convert.f_from secret_key_serialized
    in
    Core.Result.Result_Ok (Libcrux.Kem.Kyber.Types.impl__from private_key public_key)

let encapsulate
      (#v_K #v_CIPHERTEXT_SIZE #v_PUBLIC_KEY_SIZE #v_T_AS_NTT_ENCODED_SIZE #v_C1_SIZE #v_C2_SIZE #v_VECTOR_U_COMPRESSION_FACTOR #v_VECTOR_V_COMPRESSION_FACTOR #v_VECTOR_U_BLOCK_LEN #v_ETA1 #v_ETA1_RANDOMNESS_SIZE #v_ETA2 #v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: t_KyberPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
    : Core.Result.t_Result (t_KyberCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
      t_BadRejectionSamplingRandomnessError =
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (Rust_primitives.unsize randomness <: t_Slice u8
      )
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE })
            <:
            t_Slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H (Rust_primitives.unsize (impl_29__as_slice
                          public_key
                        <:
                        t_Array u8 v_PUBLIC_KEY_SIZE)
                    <:
                    t_Slice u8)
                <:
                t_Array u8 (sz 32))
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8)
      Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
  in
  let ciphertext, sampling_a_error:(t_KyberCiphertext v_CIPHERTEXT_SIZE &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt (Rust_primitives.unsize (impl_29__as_slice public_key
            <:
            t_Array u8 v_PUBLIC_KEY_SIZE)
        <:
        t_Slice u8)
      randomness
      pseudorandomness
  in
  if Core.Option.impl__is_some sampling_a_error
  then Core.Result.Result_Err (Core.Option.impl__unwrap sampling_a_error)
  else
    Core.Result.Result_Ok
    (ciphertext,
      Core.Result.impl__unwrap (Core.Convert.f_try_into shared_secret
          <:
          Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError))

let decapsulate
      (#v_K #v_SECRET_KEY_SIZE #v_CPA_SECRET_KEY_SIZE #v_PUBLIC_KEY_SIZE #v_CIPHERTEXT_SIZE #v_T_AS_NTT_ENCODED_SIZE #v_C1_SIZE #v_C2_SIZE #v_VECTOR_U_COMPRESSION_FACTOR #v_VECTOR_V_COMPRESSION_FACTOR #v_C1_BLOCK_SIZE #v_ETA1 #v_ETA1_RANDOMNESS_SIZE #v_ETA2 #v_ETA2_RANDOMNESS_SIZE #v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (secret_key: t_KyberPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : t_Array u8 (sz 32) =
  let ind_cpa_secret_key, secret_key:(t_Slice u8 & t_Slice u8) =
    impl_19__split_at secret_key v_CPA_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at secret_key v_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at secret_key Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
  in
  let decrypted:t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Ind_cpa.decrypt ind_cpa_secret_key ciphertext
  in
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (Rust_primitives.unsize decrypted <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE })
            <:
            t_Slice u8)
          ind_cpa_public_key_hash
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8)
      Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
  in
  let (to_hash: t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE):t_Array u8
    v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Libcrux.Kem.Kyber.Conversions.into_padded_array implicit_rejection_value
  in
  let to_hash:t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE })
            <:
            t_Slice u8)
          (Core.Convert.f_as_ref ciphertext <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let (implicit_rejection_shared_secret: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let expected_ciphertext, _:(t_KyberCiphertext v_CIPHERTEXT_SIZE &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt ind_cpa_public_key decrypted pseudorandomness
  in
  let selector:u8 =
    Libcrux.Kem.Kyber.Constant_time_ops.compare_ciphertexts_in_constant_time (Core.Convert.f_as_ref ciphertext

        <:
        t_Slice u8)
      (Core.Convert.f_as_ref expected_ciphertext <: t_Slice u8)
  in
  Libcrux.Kem.Kyber.Constant_time_ops.select_shared_secret_in_constant_time shared_secret
    (Rust_primitives.unsize implicit_rejection_shared_secret <: t_Slice u8)
    selector