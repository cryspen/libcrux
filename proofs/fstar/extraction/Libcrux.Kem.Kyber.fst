module Libcrux.Kem.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_KyberCiphertext (#v_SIZE: usize) = { f_value:array u8 v_SIZE }

let impl (#v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberCiphertext v_SIZE) (slice u8) =
  {
    f_impl__as_ref
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_1 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberCiphertext v_SIZE) (array u8 v_SIZE) =
  { f_impl_1__from = fun (#v_SIZE: usize) (value: array u8 v_SIZE) -> { f_value = value } }

let impl_2 (#v_SIZE: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberCiphertext v_SIZE) =
  { f_impl_2__from = fun (#v_SIZE: usize) (value: t_KyberCiphertext v_SIZE) -> value.f_value }

let impl_3 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberCiphertext v_SIZE) (slice u8) =
  {
    f_impl_3__Error = Core.Array.t_TryFromSliceError;
    f_impl_3__try_from
    =
    fun (#v_SIZE: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist6:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.f_branch (Core.Convert.f_try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _.f_Error)
            with
            | Core.Ops.Control_flow.ControlFlow_Break
              { Core.Ops.Control_flow.ControlFlow._0 = residual } ->
              let* hoist5:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (t_KyberCiphertext v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist5)
            | Core.Ops.Control_flow.ControlFlow_Continue
              { Core.Ops.Control_flow.ControlFlow._0 = v_val } ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist7:t_KyberCiphertext v_SIZE = { f_value = hoist6 } in
            Core.Result.Result_Ok hoist7))
  }

let impl_4 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) usize =
  {
    f_impl_4__Output = u8;
    f_impl_4__index
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_5 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_impl_5__Output = slice u8;
    f_impl_5__index
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_6 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_impl_6__Output = slice u8;
    f_impl_6__index
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_7 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_impl_7__Output = slice u8;
    f_impl_7__index
    =
    fun
      (#v_SIZE: usize)
      (self: t_KyberCiphertext v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.f_value.[ range ]
  }

let impl_8__as_slice (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) : array u8 v_SIZE =
  self.f_value

let impl_8__split_at (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: slice u8) mid

let impl_8__len (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) : usize = v_SIZE

type t_KyberSharedSecret (#v_SIZE: usize) = { f_value:array u8 v_SIZE }

let impl_9 (#v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberSharedSecret v_SIZE) (slice u8) =
  {
    f_impl_9__as_ref
    =
    fun (#v_SIZE: usize) (self: t_KyberSharedSecret v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_10 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberSharedSecret v_SIZE) (array u8 v_SIZE) =
  { f_impl_10__from = fun (#v_SIZE: usize) (value: array u8 v_SIZE) -> { f_value = value } }

let impl_11 (#v_SIZE: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberSharedSecret v_SIZE) =
  { f_impl_11__from = fun (#v_SIZE: usize) (value: t_KyberSharedSecret v_SIZE) -> value.f_value }

let impl_12 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberSharedSecret v_SIZE) (slice u8) =
  {
    f_impl_12__Error = Core.Array.t_TryFromSliceError;
    f_impl_12__try_from
    =
    fun (#v_SIZE: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist9:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.f_branch (Core.Convert.f_try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _.f_Error)
            with
            | Core.Ops.Control_flow.ControlFlow_Break
              { Core.Ops.Control_flow.ControlFlow._0 = residual } ->
              let* hoist8:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (t_KyberSharedSecret v_SIZE) Core.Array.t_TryFromSliceError
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist8)
            | Core.Ops.Control_flow.ControlFlow_Continue
              { Core.Ops.Control_flow.ControlFlow._0 = v_val } ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist10:t_KyberSharedSecret v_SIZE = { f_value = hoist9 } in
            Core.Result.Result_Ok hoist10))
  }

let impl_13 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) usize =
  {
    f_impl_13__Output = u8;
    f_impl_13__index
    =
    fun (#v_SIZE: usize) (self: t_KyberSharedSecret v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_14 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_impl_14__Output = slice u8;
    f_impl_14__index
    =
    fun (#v_SIZE: usize) (self: t_KyberSharedSecret v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_15 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_impl_15__Output = slice u8;
    f_impl_15__index
    =
    fun
      (#v_SIZE: usize)
      (self: t_KyberSharedSecret v_SIZE)
      (range: Core.Ops.Range.t_RangeTo usize)
      ->
      self.f_value.[ range ]
  }

let impl_16 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberSharedSecret v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_impl_16__Output = slice u8;
    f_impl_16__index
    =
    fun
      (#v_SIZE: usize)
      (self: t_KyberSharedSecret v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.f_value.[ range ]
  }

let impl_17__as_slice (#v_SIZE: usize) (self: t_KyberSharedSecret v_SIZE) : array u8 v_SIZE =
  self.f_value

let impl_17__split_at (#v_SIZE: usize) (self: t_KyberSharedSecret v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: slice u8) mid

let impl_17__len (#v_SIZE: usize) (self: t_KyberSharedSecret v_SIZE) : usize = v_SIZE

type t_KyberPrivateKey (#v_SIZE: usize) = { f_value:array u8 v_SIZE }

let impl_18 (#v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberPrivateKey v_SIZE) (slice u8) =
  {
    f_impl_18__as_ref
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_19 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberPrivateKey v_SIZE) (array u8 v_SIZE) =
  { f_impl_19__from = fun (#v_SIZE: usize) (value: array u8 v_SIZE) -> { f_value = value } }

let impl_20 (#v_SIZE: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberPrivateKey v_SIZE) =
  { f_impl_20__from = fun (#v_SIZE: usize) (value: t_KyberPrivateKey v_SIZE) -> value.f_value }

let impl_21 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberPrivateKey v_SIZE) (slice u8) =
  {
    f_impl_21__Error = Core.Array.t_TryFromSliceError;
    f_impl_21__try_from
    =
    fun (#v_SIZE: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist12:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.f_branch (Core.Convert.f_try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _.f_Error)
            with
            | Core.Ops.Control_flow.ControlFlow_Break
              { Core.Ops.Control_flow.ControlFlow._0 = residual } ->
              let* hoist11:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (t_KyberPrivateKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist11)
            | Core.Ops.Control_flow.ControlFlow_Continue
              { Core.Ops.Control_flow.ControlFlow._0 = v_val } ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist13:t_KyberPrivateKey v_SIZE = { f_value = hoist12 } in
            Core.Result.Result_Ok hoist13))
  }

let impl_22 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) usize =
  {
    f_impl_22__Output = u8;
    f_impl_22__index
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_23 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_impl_23__Output = slice u8;
    f_impl_23__index
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_24 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_impl_24__Output = slice u8;
    f_impl_24__index
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_25 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_impl_25__Output = slice u8;
    f_impl_25__index
    =
    fun
      (#v_SIZE: usize)
      (self: t_KyberPrivateKey v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.f_value.[ range ]
  }

let impl_26__as_slice (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) : array u8 v_SIZE =
  self.f_value

let impl_26__split_at (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: slice u8) mid

let impl_26__len (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) : usize = v_SIZE

type t_KyberPublicKey (#v_SIZE: usize) = { f_value:array u8 v_SIZE }

let impl_27 (#v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberPublicKey v_SIZE) (slice u8) =
  {
    f_impl_27__as_ref
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_28 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberPublicKey v_SIZE) (array u8 v_SIZE) =
  { f_impl_28__from = fun (#v_SIZE: usize) (value: array u8 v_SIZE) -> { f_value = value } }

let impl_29 (#v_SIZE: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_KyberPublicKey v_SIZE) =
  { f_impl_29__from = fun (#v_SIZE: usize) (value: t_KyberPublicKey v_SIZE) -> value.f_value }

let impl_30 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberPublicKey v_SIZE) (slice u8) =
  {
    f_impl_30__Error = Core.Array.t_TryFromSliceError;
    f_impl_30__try_from
    =
    fun (#v_SIZE: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist15:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.f_branch (Core.Convert.f_try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _.f_Error)
            with
            | Core.Ops.Control_flow.ControlFlow_Break
              { Core.Ops.Control_flow.ControlFlow._0 = residual } ->
              let* hoist14:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (t_KyberPublicKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist14)
            | Core.Ops.Control_flow.ControlFlow_Continue
              { Core.Ops.Control_flow.ControlFlow._0 = v_val } ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist16:t_KyberPublicKey v_SIZE = { f_value = hoist15 } in
            Core.Result.Result_Ok hoist16))
  }

let impl_31 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) usize =
  {
    f_impl_31__Output = u8;
    f_impl_31__index
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_32 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_impl_32__Output = slice u8;
    f_impl_32__index
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_33 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_impl_33__Output = slice u8;
    f_impl_33__index
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_34 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_impl_34__Output = slice u8;
    f_impl_34__index
    =
    fun
      (#v_SIZE: usize)
      (self: t_KyberPublicKey v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.f_value.[ range ]
  }

let impl_35__as_slice (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) : array u8 v_SIZE =
  self.f_value

let impl_35__split_at (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: slice u8) mid

let impl_35__len (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) : usize = v_SIZE

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
      (#v_K #v_CPA_PRIVATE_KEY_SIZE #v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE #v_BYTES_PER_RING_ELEMENT:
          usize)
      (randomness: array u8 (sz 64))
    : Core.Result.t_Result (t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      t_BadRejectionSamplingRandomnessError =
  let ind_cpa_keypair_randomness:slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = sz 0;
        Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      } ]
  in
  let implicit_rejection_value:slice u8 =
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
  let secret_key_serialized:array u8 v_PRIVATE_KEY_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.serialize_secret_key (Rust_primitives.unsize (Libcrux.Kem.Kyber.Ind_cpa.impl_8__as_slice
              ind_cpa_private_key
            <:
            array u8 v_CPA_PRIVATE_KEY_SIZE)
        <:
        slice u8)
      (Rust_primitives.unsize (impl_35__as_slice public_key <: array u8 v_PUBLIC_KEY_SIZE)
        <:
        slice u8)
      implicit_rejection_value
  in
  match sampling_a_error with
  | Core.Option.Option_Some { Core.Option.Option._0 = error } -> Core.Result.Result_Err error
  | _ ->
    let (private_key: t_KyberPrivateKey v_PRIVATE_KEY_SIZE):t_KyberPrivateKey v_PRIVATE_KEY_SIZE =
      Core.Convert.f_from secret_key_serialized
    in
    Core.Result.Result_Ok (Libcrux.Kem.Kyber.Types.impl__from private_key public_key)

let encapsulate
      (#v_K #v_SHARED_SECRET_SIZE #v_CIPHERTEXT_SIZE #v_PUBLIC_KEY_SIZE #v_T_AS_NTT_ENCODED_SIZE #v_C1_SIZE #v_C2_SIZE #v_VECTOR_U_COMPRESSION_FACTOR #v_VECTOR_V_COMPRESSION_FACTOR #v_VECTOR_U_BLOCK_LEN:
          usize)
      (public_key: t_KyberPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: array u8 v_SHARED_SECRET_SIZE)
    : Core.Result.t_Result
      (t_KyberCiphertext v_CIPHERTEXT_SIZE & t_KyberSharedSecret v_SHARED_SECRET_SIZE)
      t_BadRejectionSamplingRandomnessError =
  let randomness_hashed:array u8 (sz 32) =
    Libcrux.Kem.Kyber.Hash_functions.v_H (Rust_primitives.unsize randomness <: slice u8)
  in
  let (to_hash: array u8 (sz 64)):array u8 (sz 64) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (Rust_primitives.unsize randomness_hashed
        <:
        slice u8)
  in
  let to_hash:array u8 (sz 64) =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE })
            <:
            slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H (Rust_primitives.unsize (impl_35__as_slice
                          public_key
                        <:
                        array u8 v_PUBLIC_KEY_SIZE)
                    <:
                    slice u8)
                <:
                array u8 (sz 32))
            <:
            slice u8)
        <:
        slice u8)
  in
  let hashed:array u8 (sz 64) =
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
  in
  let k_not, pseudorandomness:(slice u8 & slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: slice u8) (sz 32)
  in
  let ciphertext, sampling_a_error:(t_KyberCiphertext v_CIPHERTEXT_SIZE &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt (Rust_primitives.unsize (impl_35__as_slice public_key
            <:
            array u8 v_PUBLIC_KEY_SIZE)
        <:
        slice u8)
      randomness_hashed
      pseudorandomness
  in
  let (to_hash: array u8 (sz 64)):array u8 (sz 64) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array k_not
  in
  let to_hash:array u8 (sz 64) =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE })
            <:
            slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H (Core.Convert.f_as_ref ciphertext

                    <:
                    slice u8)
                <:
                array u8 (sz 32))
            <:
            slice u8)
        <:
        slice u8)
  in
  let shared_secret:t_KyberSharedSecret v_SHARED_SECRET_SIZE =
    Core.Convert.f_into (Libcrux.Kem.Kyber.Hash_functions.v_KDF (Rust_primitives.unsize to_hash
            <:
            slice u8)
        <:
        array u8 v_SHARED_SECRET_SIZE)
  in
  if Core.Option.impl__is_some sampling_a_error
  then Core.Result.Result_Err (Core.Option.impl__unwrap sampling_a_error)
  else Core.Result.Result_Ok (ciphertext, shared_secret)

let decapsulate
      (#v_K #v_SECRET_KEY_SIZE #v_CPA_SECRET_KEY_SIZE #v_PUBLIC_KEY_SIZE #v_CIPHERTEXT_SIZE #v_T_AS_NTT_ENCODED_SIZE #v_C1_SIZE #v_C2_SIZE #v_VECTOR_U_COMPRESSION_FACTOR #v_VECTOR_V_COMPRESSION_FACTOR #v_C1_BLOCK_SIZE:
          usize)
      (secret_key: t_KyberPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : array u8 (sz 32) =
  let ind_cpa_secret_key, secret_key:(slice u8 & slice u8) =
    impl_26__split_at secret_key v_CPA_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(slice u8 & slice u8) =
    Core.Slice.impl__split_at secret_key v_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(slice u8 & slice u8) =
    Core.Slice.impl__split_at secret_key Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
  in
  let decrypted:array u8 (sz 32) =
    Libcrux.Kem.Kyber.Ind_cpa.decrypt ind_cpa_secret_key ciphertext
  in
  let (to_hash: array u8 (sz 64)):array u8 (sz 64) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (Rust_primitives.unsize decrypted <: slice u8)
  in
  let to_hash:array u8 (sz 64) =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE })
            <:
            slice u8)
          ind_cpa_public_key_hash
        <:
        slice u8)
  in
  let hashed:array u8 (sz 64) =
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
  in
  let k_not, pseudorandomness:(slice u8 & slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: slice u8) (sz 32)
  in
  let expected_ciphertext, _:(t_KyberCiphertext v_CIPHERTEXT_SIZE &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt ind_cpa_public_key decrypted pseudorandomness
  in
  let selector:u8 =
    Libcrux.Kem.Kyber.Constant_time_ops.compare_ciphertexts_in_constant_time (Core.Convert.f_as_ref ciphertext

        <:
        slice u8)
      (Core.Convert.f_as_ref expected_ciphertext <: slice u8)
  in
  let to_hash:array u8 (sz 32) =
    Libcrux.Kem.Kyber.Constant_time_ops.select_shared_secret_in_constant_time k_not
      implicit_rejection_value
      selector
  in
  let (to_hash: array u8 (sz 64)):array u8 (sz 64) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (Rust_primitives.unsize to_hash <: slice u8)
  in
  let to_hash:array u8 (sz 64) =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE })
            <:
            slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H (Core.Convert.f_as_ref ciphertext

                    <:
                    slice u8)
                <:
                array u8 (sz 32))
            <:
            slice u8)
        <:
        slice u8)
  in
  Libcrux.Kem.Kyber.Hash_functions.v_KDF (Rust_primitives.unsize to_hash <: slice u8)