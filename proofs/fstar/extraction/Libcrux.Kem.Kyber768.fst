module Libcrux.Kem.Kyber768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_SHARED_SECRET_SIZE: usize = Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_MESSAGE_SIZE

let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +. v_SHARED_SECRET_SIZE

let v_PUBLIC_KEY_SIZE: usize = Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE_768_

let v_SECRET_KEY_SIZE_512_: usize =
  ((Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_SECRET_KEY_SIZE_512_ +.
      Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE_512_
      <:
      usize) +.
    Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
    <:
    usize) +.
  v_SHARED_SECRET_SIZE

let v_SECRET_KEY_SIZE_768_: usize =
  ((Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_SECRET_KEY_SIZE_768_ +.
      Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE_768_
      <:
      usize) +.
    Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
    <:
    usize) +.
  v_SHARED_SECRET_SIZE

let v_SECRET_KEY_SIZE_1024_: usize =
  ((Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_SECRET_KEY_SIZE_1024_ +.
      Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE_1024_
      <:
      usize) +.
    Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
    <:
    usize) +.
  v_SHARED_SECRET_SIZE

let v_CIPHERTEXT_SIZE: usize = Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_CIPHERTEXT_SIZE_768_

type t_BadRejectionSamplingRandomnessError =
  | BadRejectionSamplingRandomnessError : t_BadRejectionSamplingRandomnessError

type t_KyberCiphertext = { f_value:array u8 v_SIZE }

let impl (#size: usize) : Core.Convert.t_AsRef (t_KyberCiphertext v_SIZE) (slice u8) =
  {
    as_ref
    =
    fun (#size: usize) (self: t_KyberCiphertext v_SIZE) ->
      Rust_primitives.unsize self.Libcrux.Kem.Kyber768.KyberCiphertext.f_value
  }

let impl (#size: usize) : Core.Convert.t_From (t_KyberCiphertext v_SIZE) (array u8 v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: array u8 v_SIZE) ->
      { Libcrux.Kem.Kyber768.KyberCiphertext.f_value = value }
  }

let impl (#size: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberCiphertext v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: t_KyberCiphertext v_SIZE) ->
      value.Libcrux.Kem.Kyber768.KyberCiphertext.f_value
  }

let impl (#size: usize) : Core.Convert.t_TryFrom (t_KyberCiphertext v_SIZE) (slice u8) =
  {
    error = Core.Array.t_TryFromSliceError;
    try_from
    =
    fun (#size: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist19:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.Try.branch (Core.Convert.TryInto.try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist18:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                      residual
                    <:
                    Core.Result.t_Result (t_KyberCiphertext v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist18)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist20:t_KyberCiphertext v_SIZE =
              { Libcrux.Kem.Kyber768.KyberCiphertext.f_value = hoist19 }
            in
            Core.Result.Result_Ok hoist20))
  }

let impl (#size: usize) : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) usize =
  {
    output = u8;
    index
    =
    fun (#size: usize) (self: t_KyberCiphertext v_SIZE) (index: usize) ->
      self.Libcrux.Kem.Kyber768.KyberCiphertext.f_value.[ index ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.Libcrux.Kem.Kyber768.KyberCiphertext.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.Libcrux.Kem.Kyber768.KyberCiphertext.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_RangeFrom usize) ->
      self.Libcrux.Kem.Kyber768.KyberCiphertext.f_value.[ range ]
  }

let as_slice_under_impl_11 (#size: usize) (self: t_KyberCiphertext v_SIZE) : array u8 v_SIZE =
  self.Libcrux.Kem.Kyber768.KyberCiphertext.f_value

let split_at_under_impl_11 (#size: usize) (self: t_KyberCiphertext v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.split_at_under_impl (Rust_primitives.unsize self
          .Libcrux.Kem.Kyber768.KyberCiphertext.f_value
      <:
      slice u8)
    mid

let len_under_impl_11 (#size: usize) (self: t_KyberCiphertext v_SIZE) : usize = v_SIZE

type t_KyberSharedSecret = { f_value:array u8 v_SIZE }

let impl (#size: usize) : Core.Convert.t_AsRef (t_KyberSharedSecret v_SIZE) (slice u8) =
  {
    as_ref
    =
    fun (#size: usize) (self: t_KyberSharedSecret v_SIZE) ->
      Rust_primitives.unsize self.Libcrux.Kem.Kyber768.KyberSharedSecret.f_value
  }

let impl (#size: usize) : Core.Convert.t_From (t_KyberSharedSecret v_SIZE) (array u8 v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: array u8 v_SIZE) ->
      { Libcrux.Kem.Kyber768.KyberSharedSecret.f_value = value }
  }

let impl (#size: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberSharedSecret v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: t_KyberSharedSecret v_SIZE) ->
      value.Libcrux.Kem.Kyber768.KyberSharedSecret.f_value
  }

let impl (#size: usize) : Core.Convert.t_TryFrom (t_KyberSharedSecret v_SIZE) (slice u8) =
  {
    error = Core.Array.t_TryFromSliceError;
    try_from
    =
    fun (#size: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist22:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.Try.branch (Core.Convert.TryInto.try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist21:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                      residual
                    <:
                    Core.Result.t_Result (t_KyberSharedSecret v_SIZE) Core.Array.t_TryFromSliceError
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist21)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist23:t_KyberSharedSecret v_SIZE =
              { Libcrux.Kem.Kyber768.KyberSharedSecret.f_value = hoist22 }
            in
            Core.Result.Result_Ok hoist23))
  }

let impl (#size: usize) : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) usize =
  {
    output = u8;
    index
    =
    fun (#size: usize) (self: t_KyberSharedSecret v_SIZE) (index: usize) ->
      self.Libcrux.Kem.Kyber768.KyberSharedSecret.f_value.[ index ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberSharedSecret v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.Libcrux.Kem.Kyber768.KyberSharedSecret.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberSharedSecret v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.Libcrux.Kem.Kyber768.KyberSharedSecret.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    output = slice u8;
    index
    =
    fun
      (#size: usize)
      (self: t_KyberSharedSecret v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.Libcrux.Kem.Kyber768.KyberSharedSecret.f_value.[ range ]
  }

let as_slice_under_impl_20 (#size: usize) (self: t_KyberSharedSecret v_SIZE) : array u8 v_SIZE =
  self.Libcrux.Kem.Kyber768.KyberSharedSecret.f_value

let split_at_under_impl_20 (#size: usize) (self: t_KyberSharedSecret v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.split_at_under_impl (Rust_primitives.unsize self
          .Libcrux.Kem.Kyber768.KyberSharedSecret.f_value
      <:
      slice u8)
    mid

let len_under_impl_20 (#size: usize) (self: t_KyberSharedSecret v_SIZE) : usize = v_SIZE

type t_KyberPrivateKey = { f_value:array u8 v_SIZE }

let impl (#size: usize) : Core.Convert.t_AsRef (t_KyberPrivateKey v_SIZE) (slice u8) =
  {
    as_ref
    =
    fun (#size: usize) (self: t_KyberPrivateKey v_SIZE) ->
      Rust_primitives.unsize self.Libcrux.Kem.Kyber768.KyberPrivateKey.f_value
  }

let impl (#size: usize) : Core.Convert.t_From (t_KyberPrivateKey v_SIZE) (array u8 v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: array u8 v_SIZE) ->
      { Libcrux.Kem.Kyber768.KyberPrivateKey.f_value = value }
  }

let impl (#size: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberPrivateKey v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: t_KyberPrivateKey v_SIZE) ->
      value.Libcrux.Kem.Kyber768.KyberPrivateKey.f_value
  }

let impl (#size: usize) : Core.Convert.t_TryFrom (t_KyberPrivateKey v_SIZE) (slice u8) =
  {
    error = Core.Array.t_TryFromSliceError;
    try_from
    =
    fun (#size: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist25:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.Try.branch (Core.Convert.TryInto.try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist24:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                      residual
                    <:
                    Core.Result.t_Result (t_KyberPrivateKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist24)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist26:t_KyberPrivateKey v_SIZE =
              { Libcrux.Kem.Kyber768.KyberPrivateKey.f_value = hoist25 }
            in
            Core.Result.Result_Ok hoist26))
  }

let impl (#size: usize) : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) usize =
  {
    output = u8;
    index
    =
    fun (#size: usize) (self: t_KyberPrivateKey v_SIZE) (index: usize) ->
      self.Libcrux.Kem.Kyber768.KyberPrivateKey.f_value.[ index ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.Libcrux.Kem.Kyber768.KyberPrivateKey.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.Libcrux.Kem.Kyber768.KyberPrivateKey.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeFrom usize) ->
      self.Libcrux.Kem.Kyber768.KyberPrivateKey.f_value.[ range ]
  }

let as_slice_under_impl_29 (#size: usize) (self: t_KyberPrivateKey v_SIZE) : array u8 v_SIZE =
  self.Libcrux.Kem.Kyber768.KyberPrivateKey.f_value

let split_at_under_impl_29 (#size: usize) (self: t_KyberPrivateKey v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.split_at_under_impl (Rust_primitives.unsize self
          .Libcrux.Kem.Kyber768.KyberPrivateKey.f_value
      <:
      slice u8)
    mid

let len_under_impl_29 (#size: usize) (self: t_KyberPrivateKey v_SIZE) : usize = v_SIZE

type t_CcaKeyPair = {
  f_sk:t_KyberPrivateKey v_PRIVATE_KEY_SIZE;
  f_pk:Libcrux.Kem.Kyber768.Ind_cpa.t_PublicKey v_PUBLIC_KEY_SIZE
}

let new_under_impl
      (#private_key_size #public_key_size: usize)
      (sk: array u8 v_PRIVATE_KEY_SIZE)
      (pk: array u8 v_PUBLIC_KEY_SIZE)
    : t_CcaKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
  {
    Libcrux.Kem.Kyber768.CcaKeyPair.f_sk = Core.Convert.Into.into sk;
    Libcrux.Kem.Kyber768.CcaKeyPair.f_pk = Core.Convert.Into.into pk
  }

let from_under_impl
      (#private_key_size #public_key_size: usize)
      (sk: t_KyberPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: Libcrux.Kem.Kyber768.Ind_cpa.t_PublicKey v_PUBLIC_KEY_SIZE)
    : t_CcaKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
  { Libcrux.Kem.Kyber768.CcaKeyPair.f_sk = sk; Libcrux.Kem.Kyber768.CcaKeyPair.f_pk = pk }

let public_key_under_impl
      (#private_key_size #public_key_size: usize)
      (self: t_CcaKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Libcrux.Kem.Kyber768.Ind_cpa.t_PublicKey v_PUBLIC_KEY_SIZE =
  self.Libcrux.Kem.Kyber768.CcaKeyPair.f_pk

let private_key_under_impl
      (#private_key_size #public_key_size: usize)
      (self: t_CcaKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_KyberPrivateKey v_PRIVATE_KEY_SIZE = self.Libcrux.Kem.Kyber768.CcaKeyPair.f_sk

let pk_under_impl
      (#private_key_size #public_key_size: usize)
      (self: t_CcaKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : array u8 v_PUBLIC_KEY_SIZE =
  Libcrux.Kem.Kyber768.Ind_cpa.as_slice_under_impl_14 self.Libcrux.Kem.Kyber768.CcaKeyPair.f_pk

let sk_under_impl
      (#private_key_size #public_key_size: usize)
      (self: t_CcaKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : array u8 v_PRIVATE_KEY_SIZE = as_slice_under_impl_29 self.Libcrux.Kem.Kyber768.CcaKeyPair.f_sk

let t_CcaKeyPair512 = t_CcaKeyPair 768sz 800sz

let t_CcaKeyPair768 = t_CcaKeyPair 1152sz 1184sz

let t_CcaKeyPair1024 = t_CcaKeyPair 1536sz 1568sz

type t_KyberKeyPair =
  | KyberKeyPair_Kyber512 :
      t_KyberPrivateKey 768sz ->
      Libcrux.Kem.Kyber768.Ind_cpa.t_PublicKey 800sz
    -> t_KyberKeyPair
  | KyberKeyPair_Kyber768 :
      t_KyberPrivateKey 1152sz ->
      Libcrux.Kem.Kyber768.Ind_cpa.t_PublicKey 1184sz
    -> t_KyberKeyPair
  | KyberKeyPair_Kyber1024 :
      t_KyberPrivateKey 1536sz ->
      Libcrux.Kem.Kyber768.Ind_cpa.t_PublicKey 1568sz
    -> t_KyberKeyPair

let pk_under_impl_1 (self: t_KyberKeyPair) : slice u8 =
  match self with
  | KyberKeyPair_Kyber512 _ pk -> Core.Convert.AsRef.as_ref pk
  | KyberKeyPair_Kyber768 _ pk -> Core.Convert.AsRef.as_ref pk
  | KyberKeyPair_Kyber1024 _ pk -> Core.Convert.AsRef.as_ref pk

let sk_under_impl_1 (self: t_KyberKeyPair) : slice u8 =
  match self with
  | KyberKeyPair_Kyber512 sk _ -> Core.Convert.AsRef.as_ref sk
  | KyberKeyPair_Kyber768 sk _ -> Core.Convert.AsRef.as_ref sk
  | KyberKeyPair_Kyber1024 sk _ -> Core.Convert.AsRef.as_ref sk

let generate_key_pair_768_ (randomness: array u8 64sz)
    : Core.Result.t_Result (t_CcaKeyPair 2400sz 1184sz) t_BadRejectionSamplingRandomnessError =
  generate_keypair randomness

let generate_keypair
      (#k #cpa_private_key_size #private_key_size #public_key_size #bytes_per_ring_element: usize)
      (randomness: array u8 64sz)
    : Core.Result.t_Result (t_CcaKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      t_BadRejectionSamplingRandomnessError =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ind_cpa_keypair_randomness:slice u8 =
        randomness.[ {
            Core.Ops.Range.Range.f_start = 0sz;
            Core.Ops.Range.Range.f_end
            =
            Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
          } ]
      in
      let implicit_rejection_value:slice u8 =
        randomness.[ {
            Core.Ops.Range.RangeFrom.f_start
            =
            Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
          } ]
      in
      let* ind_cpa_private_key, public_key:(Libcrux.Kem.Kyber768.Ind_cpa.t_PrivateKey
        v_CPA_PRIVATE_KEY_SIZE &
        Libcrux.Kem.Kyber768.Ind_cpa.t_PublicKey v_PUBLIC_KEY_SIZE) =
        match
          Core.Ops.Try_trait.Try.branch (Libcrux.Kem.Kyber768.Ind_cpa.generate_keypair ind_cpa_keypair_randomness

              <:
              Core.Result.t_Result
                (Libcrux.Kem.Kyber768.Ind_cpa.t_PrivateKey v_CPA_PRIVATE_KEY_SIZE &
                  Libcrux.Kem.Kyber768.Ind_cpa.t_PublicKey v_PUBLIC_KEY_SIZE)
                t_BadRejectionSamplingRandomnessError)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist27:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                  residual
                <:
                Core.Result.t_Result (t_CcaKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
                  t_BadRejectionSamplingRandomnessError)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist27)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let secret_key_serialized:array u8 v_PRIVATE_KEY_SIZE =
          Libcrux.Kem.Kyber768.Ind_cpa.serialize_secret_key (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Ind_cpa.as_slice_under_impl_23
                    ind_cpa_private_key
                  <:
                  array u8 v_CPA_PRIVATE_KEY_SIZE)
              <:
              slice u8)
            (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Ind_cpa.as_slice_under_impl_14 public_key
                  <:
                  array u8 v_PUBLIC_KEY_SIZE)
              <:
              slice u8)
            implicit_rejection_value
        in
        let (private_key: t_KyberPrivateKey v_PRIVATE_KEY_SIZE):t_KyberPrivateKey v_PRIVATE_KEY_SIZE
        =
          Core.Convert.From.from secret_key_serialized
        in
        Core.Result.Result_Ok (from_under_impl private_key public_key)))

let encapsulate_768_
      (public_key: Libcrux.Kem.Kyber768.Ind_cpa.t_PublicKey 1184sz)
      (randomness: array u8 32sz)
    : Core.Result.t_Result (t_KyberCiphertext 1088sz & t_KyberSharedSecret 32sz)
      t_BadRejectionSamplingRandomnessError = encapsulate public_key randomness

let encapsulate
      (#shared_secret_size #ciphertext_size #public_key_size: usize)
      (public_key: Libcrux.Kem.Kyber768.Ind_cpa.t_PublicKey v_PUBLIC_KEY_SIZE)
      (randomness: array u8 v_SHARED_SECRET_SIZE)
    : Core.Result.t_Result
      (t_KyberCiphertext v_CIPHERTEXT_SIZE & t_KyberSharedSecret v_SHARED_SECRET_SIZE)
      t_BadRejectionSamplingRandomnessError =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let randomness_hashed:array u8 32sz =
        Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H (Rust_primitives.unsize randomness
            <:
            slice u8)
      in
      let (to_hash: array u8 64sz):array u8 64sz =
        Libcrux.Kem.Kyber768.Conversions.into_padded_array (Rust_primitives.unsize randomness_hashed
            <:
            slice u8)
      in
      let to_hash:array u8 64sz =
        Rust_primitives.Hax.update_at to_hash
          ({
              Core.Ops.Range.RangeFrom.f_start
              =
              Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
            })
          (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
                  ({
                      Core.Ops.Range.RangeFrom.f_start
                      =
                      Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
                    })
                <:
                slice u8)
              (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H (Rust_primitives.unsize
                          (Libcrux.Kem.Kyber768.Ind_cpa.as_slice_under_impl_14 public_key
                            <:
                            array u8 v_PUBLIC_KEY_SIZE)
                        <:
                        slice u8)
                    <:
                    array u8 32sz)
                <:
                slice u8)
            <:
            slice u8)
      in
      let hashed:array u8 64sz =
        Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_G (Rust_primitives.unsize to_hash
            <:
            slice u8)
      in
      let k_not, pseudorandomness:(slice u8 & slice u8) =
        Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8) 32sz
      in
      let* ciphertext:t_KyberCiphertext v_CIPHERTEXT_SIZE =
        match
          Core.Ops.Try_trait.Try.branch (Libcrux.Kem.Kyber768.Ind_cpa.encrypt (Rust_primitives.unsize
                    (Libcrux.Kem.Kyber768.Ind_cpa.as_slice_under_impl_14 public_key
                      <:
                      array u8 v_PUBLIC_KEY_SIZE)
                  <:
                  slice u8)
                randomness_hashed
                pseudorandomness
              <:
              Core.Result.t_Result (t_KyberCiphertext v_CIPHERTEXT_SIZE)
                t_BadRejectionSamplingRandomnessError)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist28:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                  residual
                <:
                Core.Result.t_Result
                  (t_KyberCiphertext v_CIPHERTEXT_SIZE & t_KyberSharedSecret v_SHARED_SECRET_SIZE)
                  t_BadRejectionSamplingRandomnessError)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist28)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let (to_hash: array u8 64sz):array u8 64sz =
          Libcrux.Kem.Kyber768.Conversions.into_padded_array k_not
        in
        let to_hash:array u8 64sz =
          Rust_primitives.Hax.update_at to_hash
            ({
                Core.Ops.Range.RangeFrom.f_start
                =
                Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
              })
            (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
                    ({
                        Core.Ops.Range.RangeFrom.f_start
                        =
                        Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
                      })
                  <:
                  slice u8)
                (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H (Core.Convert.AsRef.as_ref
                            ciphertext
                          <:
                          slice u8)
                      <:
                      array u8 32sz)
                  <:
                  slice u8)
              <:
              slice u8)
        in
        let shared_secret:t_KyberSharedSecret v_SHARED_SECRET_SIZE =
          Core.Convert.Into.into (Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_KDF (Rust_primitives.unsize
                    to_hash
                  <:
                  slice u8)
              <:
              array u8 v_SHARED_SECRET_SIZE)
        in
        Core.Result.Result_Ok (ciphertext, shared_secret)))

let decapsulate_768_ (secret_key: t_KyberPrivateKey 2400sz) (ciphertext: t_KyberCiphertext 1088sz)
    : array u8 32sz = decapsulate secret_key ciphertext

let decapsulate
      (#k #secret_key_size #ciphertext_size: usize)
      (secret_key: t_KyberPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : array u8 32sz =
  let ind_cpa_secret_key, secret_key:(slice u8 & slice u8) =
    split_at_under_impl_29 secret_key Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_SECRET_KEY_SIZE_768_
  in
  let ind_cpa_public_key, secret_key:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl secret_key
      Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE_768_
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl secret_key
      Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
  in
  let decrypted:array u8 32sz =
    Libcrux.Kem.Kyber768.Ind_cpa.decrypt ind_cpa_secret_key ciphertext
  in
  let (to_hash: array u8 64sz):array u8 64sz =
    Libcrux.Kem.Kyber768.Conversions.into_padded_array (Rust_primitives.unsize decrypted <: slice u8
      )
  in
  let to_hash:array u8 64sz =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.RangeFrom.f_start = Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_MESSAGE_SIZE }
      )
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
              ({
                  Core.Ops.Range.RangeFrom.f_start
                  =
                  Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_MESSAGE_SIZE
                })
            <:
            slice u8)
          ind_cpa_public_key_hash
        <:
        slice u8)
  in
  let hashed:array u8 64sz =
    Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
  in
  let k_not, pseudorandomness:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8) 32sz
  in
  let expected_ciphertext_result:Core.Result.t_Result (t_KyberCiphertext v_CIPHERTEXT_SIZE)
    t_BadRejectionSamplingRandomnessError =
    Libcrux.Kem.Kyber768.Ind_cpa.encrypt ind_cpa_public_key decrypted pseudorandomness
  in
  let to_hash:array u8 32sz =
    match expected_ciphertext_result with
    | Core.Result.Result_Ok expected_ciphertext ->
      let selector:u8 =
        Libcrux.Kem.Kyber768.Constant_time_ops.compare_ciphertexts_in_constant_time (Core.Convert.AsRef.as_ref
              ciphertext
            <:
            slice u8)
          (Core.Convert.AsRef.as_ref expected_ciphertext <: slice u8)
      in
      Libcrux.Kem.Kyber768.Constant_time_ops.select_shared_secret_in_constant_time k_not
        implicit_rejection_value
        selector
    | _ ->
      let out:array u8 32sz = Rust_primitives.Hax.repeat 0uy 32sz in
      let out:array u8 32sz =
        Rust_primitives.Hax.update_at out
          Core.Ops.Range.RangeFull
          (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut out
                  Core.Ops.Range.RangeFull
                <:
                slice u8)
              implicit_rejection_value
            <:
            slice u8)
      in
      out
  in
  let (to_hash: array u8 64sz):array u8 64sz =
    Libcrux.Kem.Kyber768.Conversions.into_padded_array (Rust_primitives.unsize to_hash <: slice u8)
  in
  let to_hash:array u8 64sz =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.RangeFrom.f_start = v_SHARED_SECRET_SIZE })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.RangeFrom.f_start = v_SHARED_SECRET_SIZE })
            <:
            slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H (Core.Convert.AsRef.as_ref
                      ciphertext
                    <:
                    slice u8)
                <:
                array u8 32sz)
            <:
            slice u8)
        <:
        slice u8)
  in
  Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_KDF (Rust_primitives.unsize to_hash <: slice u8)