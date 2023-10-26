module Libcrux.Kem.Kyber.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_KyberCiphertext (#v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

let impl_1 (#v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberCiphertext v_SIZE) (t_Slice u8) =
  {
    f_as_ref
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_2 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberCiphertext v_SIZE) (t_Array u8 v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = value } }

let impl_3 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberCiphertext v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from
    =
    fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = Core.Clone.f_clone value }
  }

let impl_4 (#v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_KyberCiphertext v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_KyberCiphertext v_SIZE) -> value.f_value }

let impl_5 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberCiphertext v_SIZE) (t_Slice u8) =
  {
    f_Error = Core.Array.t_TryFromSliceError;
    f_try_from
    =
    fun (#v_SIZE: usize) (value: t_Slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist3:t_Array u8 v_SIZE =
            match
              Core.Ops.Try_trait.f_branch (Core.Convert.f_try_into value
                  <:
                  Core.Result.t_Result (t_Array u8 v_SIZE) Core.Array.t_TryFromSliceError)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist2:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (t_KyberCiphertext v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist2)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist4:t_KyberCiphertext v_SIZE = { f_value = hoist3 } in
            Core.Result.Result_Ok hoist4))
  }

let impl_6 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) usize =
  {
    f_Output = u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_7 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_8 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberCiphertext v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_9 (#v_SIZE: usize)
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

let impl_10__as_slice (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

let impl_10__split_at (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (mid: usize)
    : (t_Slice u8 & t_Slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: t_Slice u8) mid

let impl_10__len (#v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) : usize = v_SIZE

type t_KyberPrivateKey (#v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

let impl_11 (#v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberPrivateKey v_SIZE) (t_Slice u8) =
  {
    f_as_ref
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_12 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = value } }

let impl_13 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from
    =
    fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = Core.Clone.f_clone value }
  }

let impl_14 (#v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_KyberPrivateKey v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_KyberPrivateKey v_SIZE) -> value.f_value }

let impl_15 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberPrivateKey v_SIZE) (t_Slice u8) =
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
                    Core.Result.t_Result (t_KyberPrivateKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist5)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist7:t_KyberPrivateKey v_SIZE = { f_value = hoist6 } in
            Core.Result.Result_Ok hoist7))
  }

let impl_16 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) usize =
  {
    f_Output = u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_17 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_18 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPrivateKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_19 (#v_SIZE: usize)
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

let impl_20__as_slice (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

let impl_20__split_at (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (mid: usize)
    : (t_Slice u8 & t_Slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: t_Slice u8) mid

let impl_20__len (#v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) : usize = v_SIZE

type t_KyberPublicKey (#v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

let impl_21 (#v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberPublicKey v_SIZE) (t_Slice u8) =
  {
    f_as_ref
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_22 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberPublicKey v_SIZE) (t_Array u8 v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = value } }

let impl_23 (#v_SIZE: usize) : Core.Convert.t_From (t_KyberPublicKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from
    =
    fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = Core.Clone.f_clone value }
  }

let impl_24 (#v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_KyberPublicKey v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_KyberPublicKey v_SIZE) -> value.f_value }

let impl_25 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberPublicKey v_SIZE) (t_Slice u8) =
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
                    Core.Result.t_Result (t_KyberPublicKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist8)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist10:t_KyberPublicKey v_SIZE = { f_value = hoist9 } in
            Core.Result.Result_Ok hoist10))
  }

let impl_26 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) usize =
  {
    f_Output = u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_27 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_28 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_KyberPublicKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_29 (#v_SIZE: usize)
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

let impl_30__as_slice (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

let impl_30__split_at (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (mid: usize)
    : (t_Slice u8 & t_Slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: t_Slice u8) mid

let impl_30__len (#v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) : usize = v_SIZE

type t_PrivateKey (#v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

let impl_31 (#v_SIZE: usize) : Core.Convert.t_AsRef (t_PrivateKey v_SIZE) (t_Slice u8) =
  {
    f_as_ref
    =
    fun (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_32 (#v_SIZE: usize) : Core.Convert.t_From (t_PrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = value } }

let impl_33 (#v_SIZE: usize) : Core.Convert.t_From (t_PrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from
    =
    fun (#v_SIZE: usize) (value: t_Array u8 v_SIZE) -> { f_value = Core.Clone.f_clone value }
  }

let impl_34 (#v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_PrivateKey v_SIZE) =
  { f_from = fun (#v_SIZE: usize) (value: t_PrivateKey v_SIZE) -> value.f_value }

let impl_35 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_PrivateKey v_SIZE) (t_Slice u8) =
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
                    Core.Result.t_Result (t_PrivateKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist11)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist13:t_PrivateKey v_SIZE = { f_value = hoist12 } in
            Core.Result.Result_Ok hoist13))
  }

let impl_36 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) usize =
  {
    f_Output = u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_37 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_38 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_39 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_Output = t_Slice u8;
    f_index
    =
    fun (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeFrom usize) ->
      self.f_value.[ range ]
  }

let impl_40__as_slice (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

let impl_40__split_at (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) (mid: usize)
    : (t_Slice u8 & t_Slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: t_Slice u8) mid

let impl_40__len (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) : usize = v_SIZE

type t_KyberKeyPair (#v_PRIVATE_KEY_SIZE: usize) (#v_PUBLIC_KEY_SIZE: usize) = {
  f_sk:t_KyberPrivateKey v_PRIVATE_KEY_SIZE;
  f_pk:t_KyberPublicKey v_PUBLIC_KEY_SIZE
}

let impl__new
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (sk: t_Array u8 v_PRIVATE_KEY_SIZE)
      (pk: t_Array u8 v_PUBLIC_KEY_SIZE)
    : t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
  { f_sk = Core.Convert.f_into sk; f_pk = Core.Convert.f_into pk }

let impl__from
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (sk: t_KyberPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: t_KyberPublicKey v_PUBLIC_KEY_SIZE)
    : t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE = { f_sk = sk; f_pk = pk }

let impl__public_key
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (self: t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_KyberPublicKey v_PUBLIC_KEY_SIZE = self.f_pk

let impl__private_key
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (self: t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_KyberPrivateKey v_PRIVATE_KEY_SIZE = self.f_sk

let impl__pk
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (self: t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_Array u8 v_PUBLIC_KEY_SIZE = impl_30__as_slice self.f_pk

let impl__sk
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (self: t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_Array u8 v_PRIVATE_KEY_SIZE = impl_20__as_slice self.f_sk

type t_Error = | Error_RejectionSampling : t_Error