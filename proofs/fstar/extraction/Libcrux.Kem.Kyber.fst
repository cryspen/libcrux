module Libcrux.Kem.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_KyberCiphertext = { f_value:array u8 v_SIZE }

let impl (#size: usize) : Core.Convert.t_AsRef (t_KyberCiphertext v_SIZE) (slice u8) =
  {
    as_ref
    =
    fun (#size: usize) (self: t_KyberCiphertext v_SIZE) ->
      Rust_primitives.unsize self.Libcrux.Kem.Kyber.KyberCiphertext.f_value
  }

let impl (#size: usize) : Core.Convert.t_From (t_KyberCiphertext v_SIZE) (array u8 v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: array u8 v_SIZE) ->
      { Libcrux.Kem.Kyber.KyberCiphertext.f_value = value }
  }

let impl (#size: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberCiphertext v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: t_KyberCiphertext v_SIZE) ->
      value.Libcrux.Kem.Kyber.KyberCiphertext.f_value
  }

let impl (#size: usize) : Core.Convert.t_TryFrom (t_KyberCiphertext v_SIZE) (slice u8) =
  {
    error = Core.Array.t_TryFromSliceError;
    try_from
    =
    fun (#size: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist6:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.Try.branch (Core.Convert.TryInto.try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist5:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                      residual
                    <:
                    Core.Result.t_Result (t_KyberCiphertext v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist5)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist7:t_KyberCiphertext v_SIZE =
              { Libcrux.Kem.Kyber.KyberCiphertext.f_value = hoist6 }
            in
            Core.Result.Result_Ok hoist7))
  }

let impl (#size: usize) : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) usize =
  {
    output = u8;
    index
    =
    fun (#size: usize) (self: t_KyberCiphertext v_SIZE) (index: usize) ->
      self.Libcrux.Kem.Kyber.KyberCiphertext.f_value.[ index ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.Libcrux.Kem.Kyber.KyberCiphertext.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.Libcrux.Kem.Kyber.KyberCiphertext.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_RangeFrom usize) ->
      self.Libcrux.Kem.Kyber.KyberCiphertext.f_value.[ range ]
  }

let as_slice_under_impl_8 (#size: usize) (self: t_KyberCiphertext v_SIZE) : array u8 v_SIZE =
  self.Libcrux.Kem.Kyber.KyberCiphertext.f_value

let split_at_under_impl_8 (#size: usize) (self: t_KyberCiphertext v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.split_at_under_impl (Rust_primitives.unsize self
          .Libcrux.Kem.Kyber.KyberCiphertext.f_value
      <:
      slice u8)
    mid

let len_under_impl_8 (#size: usize) (self: t_KyberCiphertext v_SIZE) : usize = v_SIZE

type t_KyberSharedSecret = { f_value:array u8 v_SIZE }

let impl (#size: usize) : Core.Convert.t_AsRef (t_KyberSharedSecret v_SIZE) (slice u8) =
  {
    as_ref
    =
    fun (#size: usize) (self: t_KyberSharedSecret v_SIZE) ->
      Rust_primitives.unsize self.Libcrux.Kem.Kyber.KyberSharedSecret.f_value
  }

let impl (#size: usize) : Core.Convert.t_From (t_KyberSharedSecret v_SIZE) (array u8 v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: array u8 v_SIZE) ->
      { Libcrux.Kem.Kyber.KyberSharedSecret.f_value = value }
  }

let impl (#size: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberSharedSecret v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: t_KyberSharedSecret v_SIZE) ->
      value.Libcrux.Kem.Kyber.KyberSharedSecret.f_value
  }

let impl (#size: usize) : Core.Convert.t_TryFrom (t_KyberSharedSecret v_SIZE) (slice u8) =
  {
    error = Core.Array.t_TryFromSliceError;
    try_from
    =
    fun (#size: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist9:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.Try.branch (Core.Convert.TryInto.try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist8:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                      residual
                    <:
                    Core.Result.t_Result (t_KyberSharedSecret v_SIZE) Core.Array.t_TryFromSliceError
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist8)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist10:t_KyberSharedSecret v_SIZE =
              { Libcrux.Kem.Kyber.KyberSharedSecret.f_value = hoist9 }
            in
            Core.Result.Result_Ok hoist10))
  }

let impl (#size: usize) : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) usize =
  {
    output = u8;
    index
    =
    fun (#size: usize) (self: t_KyberSharedSecret v_SIZE) (index: usize) ->
      self.Libcrux.Kem.Kyber.KyberSharedSecret.f_value.[ index ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberSharedSecret v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.Libcrux.Kem.Kyber.KyberSharedSecret.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberSharedSecret v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.Libcrux.Kem.Kyber.KyberSharedSecret.f_value.[ range ]
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
      self.Libcrux.Kem.Kyber.KyberSharedSecret.f_value.[ range ]
  }

let as_slice_under_impl_17 (#size: usize) (self: t_KyberSharedSecret v_SIZE) : array u8 v_SIZE =
  self.Libcrux.Kem.Kyber.KyberSharedSecret.f_value

let split_at_under_impl_17 (#size: usize) (self: t_KyberSharedSecret v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.split_at_under_impl (Rust_primitives.unsize self
          .Libcrux.Kem.Kyber.KyberSharedSecret.f_value
      <:
      slice u8)
    mid

let len_under_impl_17 (#size: usize) (self: t_KyberSharedSecret v_SIZE) : usize = v_SIZE

type t_KyberPrivateKey = { f_value:array u8 v_SIZE }

let impl (#size: usize) : Core.Convert.t_AsRef (t_KyberPrivateKey v_SIZE) (slice u8) =
  {
    as_ref
    =
    fun (#size: usize) (self: t_KyberPrivateKey v_SIZE) ->
      Rust_primitives.unsize self.Libcrux.Kem.Kyber.KyberPrivateKey.f_value
  }

let impl (#size: usize) : Core.Convert.t_From (t_KyberPrivateKey v_SIZE) (array u8 v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: array u8 v_SIZE) ->
      { Libcrux.Kem.Kyber.KyberPrivateKey.f_value = value }
  }

let impl (#size: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberPrivateKey v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: t_KyberPrivateKey v_SIZE) ->
      value.Libcrux.Kem.Kyber.KyberPrivateKey.f_value
  }

let impl (#size: usize) : Core.Convert.t_TryFrom (t_KyberPrivateKey v_SIZE) (slice u8) =
  {
    error = Core.Array.t_TryFromSliceError;
    try_from
    =
    fun (#size: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist12:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.Try.branch (Core.Convert.TryInto.try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist11:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                      residual
                    <:
                    Core.Result.t_Result (t_KyberPrivateKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist11)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist13:t_KyberPrivateKey v_SIZE =
              { Libcrux.Kem.Kyber.KyberPrivateKey.f_value = hoist12 }
            in
            Core.Result.Result_Ok hoist13))
  }

let impl (#size: usize) : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) usize =
  {
    output = u8;
    index
    =
    fun (#size: usize) (self: t_KyberPrivateKey v_SIZE) (index: usize) ->
      self.Libcrux.Kem.Kyber.KyberPrivateKey.f_value.[ index ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.Libcrux.Kem.Kyber.KyberPrivateKey.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.Libcrux.Kem.Kyber.KyberPrivateKey.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeFrom usize) ->
      self.Libcrux.Kem.Kyber.KyberPrivateKey.f_value.[ range ]
  }

let as_slice_under_impl_26 (#size: usize) (self: t_KyberPrivateKey v_SIZE) : array u8 v_SIZE =
  self.Libcrux.Kem.Kyber.KyberPrivateKey.f_value

let split_at_under_impl_26 (#size: usize) (self: t_KyberPrivateKey v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.split_at_under_impl (Rust_primitives.unsize self
          .Libcrux.Kem.Kyber.KyberPrivateKey.f_value
      <:
      slice u8)
    mid

let len_under_impl_26 (#size: usize) (self: t_KyberPrivateKey v_SIZE) : usize = v_SIZE

type t_KyberPublicKey = { f_value:array u8 v_SIZE }

let impl (#size: usize) : Core.Convert.t_AsRef (t_KyberPublicKey v_SIZE) (slice u8) =
  {
    as_ref
    =
    fun (#size: usize) (self: t_KyberPublicKey v_SIZE) ->
      Rust_primitives.unsize self.Libcrux.Kem.Kyber.KyberPublicKey.f_value
  }

let impl (#size: usize) : Core.Convert.t_From (t_KyberPublicKey v_SIZE) (array u8 v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: array u8 v_SIZE) ->
      { Libcrux.Kem.Kyber.KyberPublicKey.f_value = value }
  }

let impl (#size: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberPublicKey v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: t_KyberPublicKey v_SIZE) ->
      value.Libcrux.Kem.Kyber.KyberPublicKey.f_value
  }

let impl (#size: usize) : Core.Convert.t_TryFrom (t_KyberPublicKey v_SIZE) (slice u8) =
  {
    error = Core.Array.t_TryFromSliceError;
    try_from
    =
    fun (#size: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist15:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.Try.branch (Core.Convert.TryInto.try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist14:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                      residual
                    <:
                    Core.Result.t_Result (t_KyberPublicKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist14)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist16:t_KyberPublicKey v_SIZE =
              { Libcrux.Kem.Kyber.KyberPublicKey.f_value = hoist15 }
            in
            Core.Result.Result_Ok hoist16))
  }

let impl (#size: usize) : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) usize =
  {
    output = u8;
    index
    =
    fun (#size: usize) (self: t_KyberPublicKey v_SIZE) (index: usize) ->
      self.Libcrux.Kem.Kyber.KyberPublicKey.f_value.[ index ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberPublicKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.Libcrux.Kem.Kyber.KyberPublicKey.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberPublicKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.Libcrux.Kem.Kyber.KyberPublicKey.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_KyberPublicKey v_SIZE) (range: Core.Ops.Range.t_RangeFrom usize) ->
      self.Libcrux.Kem.Kyber.KyberPublicKey.f_value.[ range ]
  }

let as_slice_under_impl_35 (#size: usize) (self: t_KyberPublicKey v_SIZE) : array u8 v_SIZE =
  self.Libcrux.Kem.Kyber.KyberPublicKey.f_value

let split_at_under_impl_35 (#size: usize) (self: t_KyberPublicKey v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.split_at_under_impl (Rust_primitives.unsize self
          .Libcrux.Kem.Kyber.KyberPublicKey.f_value
      <:
      slice u8)
    mid

let len_under_impl_35 (#size: usize) (self: t_KyberPublicKey v_SIZE) : usize = v_SIZE

type t_KyberKeyPair = {
  f_sk:t_KyberPrivateKey v_PRIVATE_KEY_SIZE;
  f_pk:t_KyberPublicKey v_PUBLIC_KEY_SIZE
}

type t_BadRejectionSamplingRandomnessError =
  | BadRejectionSamplingRandomnessError : t_BadRejectionSamplingRandomnessError

let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +.
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

let generate_keypair
      (#k #cpa_private_key_size #private_key_size #public_key_size #bytes_per_ring_element #eta1 #eta1_randomness_size:
          usize)
      (randomness: array u8 64sz)
    : Core.Result.t_Result (t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      t_BadRejectionSamplingRandomnessError =
  let ind_cpa_keypair_randomness:slice u8 =
    randomness.[ {
        Core.Ops.Range.Range.f_start = 0sz;
        Core.Ops.Range.Range.f_end = Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      } ]
  in
  let implicit_rejection_value:slice u8 =
    randomness.[ {
        Core.Ops.Range.RangeFrom.f_start
        =
        Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      } ]
  in
  let (ind_cpa_private_key, public_key), sampling_a_error:((Libcrux.Kem.Kyber.Ind_cpa.t_PrivateKey
      v_CPA_PRIVATE_KEY_SIZE &
      t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber.Ind_cpa.generate_keypair ind_cpa_keypair_randomness
  in
  let secret_key_serialized:array u8 v_PRIVATE_KEY_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.serialize_secret_key (Rust_primitives.unsize (Libcrux.Kem.Kyber.Ind_cpa.as_slice_under_impl_8
              ind_cpa_private_key
            <:
            array u8 v_CPA_PRIVATE_KEY_SIZE)
        <:
        slice u8)
      (Rust_primitives.unsize (as_slice_under_impl_35 public_key <: array u8 v_PUBLIC_KEY_SIZE)
        <:
        slice u8)
      implicit_rejection_value
  in
  match sampling_a_error with
  | Core.Option.Option_Some error -> Core.Result.Result_Err error
  | _ ->
    let (private_key: t_KyberPrivateKey v_PRIVATE_KEY_SIZE):t_KyberPrivateKey v_PRIVATE_KEY_SIZE =
      Core.Convert.From.from secret_key_serialized
    in
    Core.Result.Result_Ok (Libcrux.Kem.Kyber.Types.from_under_impl private_key public_key)

let encapsulate
      (#k #shared_secret_size #ciphertext_size #public_key_size #t__as_ntt_encoded_size #c1_size #c2_size #vector_u_compression_factor #vector_v_compression_factor #vector_u_block_len #eta1 #eta1_randomness_size #eta2 #eta2_randomness_size:
          usize)
      (public_key: t_KyberPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: array u8 v_SHARED_SECRET_SIZE)
    : Core.Result.t_Result
      (t_KyberCiphertext v_CIPHERTEXT_SIZE & t_KyberSharedSecret v_SHARED_SECRET_SIZE)
      t_BadRejectionSamplingRandomnessError =
  let randomness_hashed:array u8 32sz =
    Libcrux.Kem.Kyber.Hash_functions.v_H (Rust_primitives.unsize randomness <: slice u8)
  in
  let (to_hash: array u8 64sz):array u8 64sz =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (Rust_primitives.unsize randomness_hashed
        <:
        slice u8)
  in
  let to_hash:array u8 64sz =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.RangeFrom.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.RangeFrom.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE })
            <:
            slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H (Rust_primitives.unsize (as_slice_under_impl_35
                          public_key
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
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
  in
  let k_not, pseudorandomness:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8) 32sz
  in
  let ciphertext, sampling_a_error:(t_KyberCiphertext v_CIPHERTEXT_SIZE &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt (Rust_primitives.unsize (as_slice_under_impl_35 public_key
            <:
            array u8 v_PUBLIC_KEY_SIZE)
        <:
        slice u8)
      randomness_hashed
      pseudorandomness
  in
  let (to_hash: array u8 64sz):array u8 64sz =
    Libcrux.Kem.Kyber.Conversions.into_padded_array k_not
  in
  let to_hash:array u8 64sz =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.RangeFrom.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.RangeFrom.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE })
            <:
            slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H (Core.Convert.AsRef.as_ref ciphertext

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
    Core.Convert.Into.into (Libcrux.Kem.Kyber.Hash_functions.v_KDF (Rust_primitives.unsize to_hash
            <:
            slice u8)
        <:
        array u8 v_SHARED_SECRET_SIZE)
  in
  if Core.Option.is_some_under_impl sampling_a_error
  then Core.Result.Result_Err (Core.Option.unwrap_under_impl sampling_a_error)
  else Core.Result.Result_Ok (ciphertext, shared_secret)

let decapsulate
      (#k #secret_key_size #cpa_secret_key_size #public_key_size #ciphertext_size #t__as_ntt_encoded_size #c1_size #c2_size #vector_u_compression_factor #vector_v_compression_factor #c1_block_size #eta1 #eta1_randomness_size #eta2 #eta2_randomness_size:
          usize)
      (secret_key: t_KyberPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : array u8 32sz =
  let ind_cpa_secret_key, secret_key:(slice u8 & slice u8) =
    split_at_under_impl_26 secret_key v_CPA_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl secret_key v_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl secret_key Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
  in
  let decrypted:array u8 32sz = Libcrux.Kem.Kyber.Ind_cpa.decrypt ind_cpa_secret_key ciphertext in
  let (to_hash: array u8 64sz):array u8 64sz =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (Rust_primitives.unsize decrypted <: slice u8)
  in
  let to_hash:array u8 64sz =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.RangeFrom.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
              ({
                  Core.Ops.Range.RangeFrom.f_start
                  =
                  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
                })
            <:
            slice u8)
          ind_cpa_public_key_hash
        <:
        slice u8)
  in
  let hashed:array u8 64sz =
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
  in
  let k_not, pseudorandomness:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8) 32sz
  in
  let expected_ciphertext, _:(t_KyberCiphertext v_CIPHERTEXT_SIZE &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt ind_cpa_public_key decrypted pseudorandomness
  in
  let selector:u8 =
    Libcrux.Kem.Kyber.Constant_time_ops.compare_ciphertexts_in_constant_time (Core.Convert.AsRef.as_ref
          ciphertext
        <:
        slice u8)
      (Core.Convert.AsRef.as_ref expected_ciphertext <: slice u8)
  in
  let to_hash:array u8 32sz =
    Libcrux.Kem.Kyber.Constant_time_ops.select_shared_secret_in_constant_time k_not
      implicit_rejection_value
      selector
  in
  let (to_hash: array u8 64sz):array u8 64sz =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (Rust_primitives.unsize to_hash <: slice u8)
  in
  let to_hash:array u8 64sz =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.RangeFrom.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
              ({
                  Core.Ops.Range.RangeFrom.f_start
                  =
                  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
                })
            <:
            slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H (Core.Convert.AsRef.as_ref ciphertext

                    <:
                    slice u8)
                <:
                array u8 32sz)
            <:
            slice u8)
        <:
        slice u8)
  in
  Libcrux.Kem.Kyber.Hash_functions.v_KDF (Rust_primitives.unsize to_hash <: slice u8)