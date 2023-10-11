module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_PrivateKey (#v_SIZE: usize) = { f_value:array u8 v_SIZE }

let impl (#v_SIZE: usize) : Core.Convert.t_AsRef (t_PrivateKey v_SIZE) (slice u8) =
  {
    f_impl__as_ref
    =
    fun (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) -> Rust_primitives.unsize self.f_value
  }

let impl_1 (#v_SIZE: usize) : Core.Convert.t_From (t_PrivateKey v_SIZE) (array u8 v_SIZE) =
  { f_impl_1__from = fun (#v_SIZE: usize) (value: array u8 v_SIZE) -> { f_value = value } }

let impl_2 (#v_SIZE: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_PrivateKey v_SIZE) =
  { f_impl_2__from = fun (#v_SIZE: usize) (value: t_PrivateKey v_SIZE) -> value.f_value }

let impl_3 (#v_SIZE: usize) : Core.Convert.t_TryFrom (t_PrivateKey v_SIZE) (slice u8) =
  {
    f_impl_3__Error = Core.Array.t_TryFromSliceError;
    f_impl_3__try_from
    =
    fun (#v_SIZE: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist2:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.f_branch (Core.Convert.f_try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE)
                    (Core.Convert.impl_6 (slice u8) (array u8 v_SIZE)).f_Error)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist1:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (t_PrivateKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist1)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist3:t_PrivateKey v_SIZE = { f_value = hoist2 } in
            Core.Result.Result_Ok hoist3))
  }

let impl_4 (#v_SIZE: usize) : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) usize =
  {
    f_impl_4__Output = u8;
    f_impl_4__index
    =
    fun (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) (index: usize) -> self.f_value.[ index ]
  }

let impl_5 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    f_impl_5__Output = slice u8;
    f_impl_5__index
    =
    fun (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.f_value.[ range ]
  }

let impl_6 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    f_impl_6__Output = slice u8;
    f_impl_6__index
    =
    fun (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.f_value.[ range ]
  }

let impl_7 (#v_SIZE: usize)
    : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_impl_7__Output = slice u8;
    f_impl_7__index
    =
    fun (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeFrom usize) ->
      self.f_value.[ range ]
  }

let impl_8__as_slice (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) : array u8 v_SIZE = self.f_value

let impl_8__split_at (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: slice u8) mid

let impl_8__len (#v_SIZE: usize) (self: t_PrivateKey v_SIZE) : usize = v_SIZE

let sample_matrix_A (#v_K: usize) (seed: array u8 (sz 34)) (transpose: bool)
    : (array (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
      Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
  let v_A_transpose:array (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K
  =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__ZERO
          v_K
        <:
        array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
      v_K
  in
  let sampling_A_error:Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError
  =
    Core.Option.Option_None
  in
  let v_A_transpose, sampling_A_error:(array
      (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (v_A_transpose, sampling_A_error)
      (fun (v_A_transpose, sampling_A_error) i ->
          let seeds:array (array u8 (sz 34)) v_K = Rust_primitives.Hax.repeat seed v_K in
          let seeds:array (array u8 (sz 34)) v_K =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = sz 0;
                      Core.Ops.Range.f_end = v_K
                    })
                <:
                (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
              seeds
              (fun seeds j ->
                  let seeds:array (array u8 (sz 34)) v_K =
                    Rust_primitives.Hax.update_at seeds
                      j
                      (Rust_primitives.Hax.update_at (seeds.[ j ] <: array u8 (sz 34))
                          (sz 32)
                          (cast i <: u8)
                        <:
                        array u8 (sz 34))
                  in
                  let seeds:array (array u8 (sz 34)) v_K =
                    Rust_primitives.Hax.update_at seeds
                      j
                      (Rust_primitives.Hax.update_at (seeds.[ j ] <: array u8 (sz 34))
                          (sz 33)
                          (cast j <: u8)
                        <:
                        array u8 (sz 34))
                  in
                  seeds)
          in
          let xof_bytes:array (array u8 (sz 840)) v_K =
            Libcrux.Kem.Kyber.Hash_functions.v_XOFx4 seeds
          in
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = v_K
                  })
              <:
              (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
            (v_A_transpose, sampling_A_error)
            (fun (v_A_transpose, sampling_A_error) j ->
                let sampled, error:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
                  Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
                  Libcrux.Kem.Kyber.Sampling.sample_from_uniform_distribution (xof_bytes.[ j ]
                      <:
                      array u8 (sz 840))
                in
                let sampling_A_error:Core.Option.t_Option
                Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
                  if Core.Option.impl__is_some error
                  then
                    let sampling_A_error:Core.Option.t_Option
                    Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
                      error
                    in
                    sampling_A_error
                  else sampling_A_error
                in
                if transpose
                then
                  let v_A_transpose:array
                    (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K =
                    Rust_primitives.Hax.update_at v_A_transpose
                      j
                      (Rust_primitives.Hax.update_at (v_A_transpose.[ j ]
                            <:
                            array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
                          i
                          sampled
                        <:
                        array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
                  in
                  v_A_transpose, sampling_A_error
                else
                  let v_A_transpose:array
                    (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K =
                    Rust_primitives.Hax.update_at v_A_transpose
                      i
                      (Rust_primitives.Hax.update_at (v_A_transpose.[ i ]
                            <:
                            array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
                          j
                          sampled
                        <:
                        array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
                  in
                  v_A_transpose, sampling_A_error))
  in
  v_A_transpose, sampling_A_error

let cbd (#v_K #v_ETA #v_ETA_RANDOMNESS_SIZE: usize) (prf_input: array u8 (sz 33))
    : (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K & u8) =
  let domain_separator:u8 = 0uy in
  let re_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__ZERO v_K
  in
  let domain_separator, prf_input, re_as_ntt:(u8 & array u8 (sz 33) &
    array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (domain_separator, prf_input, re_as_ntt)
      (fun (domain_separator, prf_input, re_as_ntt) i ->
          let prf_input:array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: array u8 v_ETA_RANDOMNESS_SIZE):array u8 v_ETA_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
          in
          let r:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution (Rust_primitives.unsize prf_output

                <:
                slice u8)
          in
          let re_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at re_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_representation r
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, prf_input, re_as_ntt)
  in
  re_as_ntt, domain_separator

let encode_12_
      (#v_K #v_OUT_LEN: usize)
      (input: array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : array u8 v_OUT_LEN =
  let out:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let out:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Iter.Traits.Collect.f_into_iter input
                <:
                (Core.Array.Iter.impl Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
                  .f_IntoIter)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                v_K))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                v_K)))
          .f_IntoIter)
      out
      (fun out (i, re) ->
          Rust_primitives.Hax.update_at out
            ({
                Core.Ops.Range.f_start
                =
                i *! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                Core.Ops.Range.f_end
                =
                (i +! sz 1 <: usize) *! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                usize
              })
            (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut out
                    ({
                        Core.Ops.Range.f_start
                        =
                        i *! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! sz 1 <: usize) *! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                        <:
                        usize
                      })
                  <:
                  slice u8)
                (Rust_primitives.unsize (Libcrux.Kem.Kyber.Serialize.serialize_little_endian re
                      <:
                      array u8 (sz 384))
                  <:
                  slice u8)
              <:
              slice u8)
          <:
          array u8 v_OUT_LEN)
  in
  out

let generate_keypair
      (#v_K #v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE #v_BYTES_PER_RING_ELEMENT #v_ETA1 #v_ETA1_RANDOMNESS_SIZE:
          usize)
      (key_generation_seed: slice u8)
    : ((t_PrivateKey v_PRIVATE_KEY_SIZE & Libcrux.Kem.Kyber.t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
      Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
  let (prf_input: array u8 (sz 33)):array u8 (sz 33) = Rust_primitives.Hax.repeat 0uy (sz 33) in
  let secret_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__ZERO v_K
  in
  let error_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__ZERO v_K
  in
  let (domain_separator: u8):u8 = 0uy in
  let hashed:array u8 (sz 64) = Libcrux.Kem.Kyber.Hash_functions.v_G key_generation_seed in
  let seed_for_A, seed_for_secret_and_error:(slice u8 & slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: slice u8) (sz 32)
  in
  let v_A_transpose, sampling_A_error:(array
      (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
    sample_matrix_A (Libcrux.Kem.Kyber.Conversions.into_padded_array seed_for_A <: array u8 (sz 34))
      true
  in
  let prf_input:array u8 (sz 33) =
    Rust_primitives.Hax.update_at prf_input
      ({
          Core.Ops.Range.f_start = sz 0;
          Core.Ops.Range.f_end = Core.Slice.impl__len seed_for_secret_and_error <: usize
        })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut prf_input
              ({
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = Core.Slice.impl__len seed_for_secret_and_error <: usize
                })
            <:
            slice u8)
          seed_for_secret_and_error
        <:
        slice u8)
  in
  let domain_separator, prf_input, secret_as_ntt:(u8 & array u8 (sz 33) &
    array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (domain_separator, prf_input, secret_as_ntt)
      (fun (domain_separator, prf_input, secret_as_ntt) i ->
          let prf_input:array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: array u8 v_ETA1_RANDOMNESS_SIZE):array u8 v_ETA1_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
          in
          let secret:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution (Rust_primitives.unsize prf_output

                <:
                slice u8)
          in
          let secret_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at secret_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_representation secret
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, prf_input, secret_as_ntt)
  in
  let domain_separator, error_as_ntt, prf_input:(u8 &
    array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K &
    array u8 (sz 33)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (domain_separator, error_as_ntt, prf_input)
      (fun (domain_separator, error_as_ntt, prf_input) i ->
          let prf_input:array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: array u8 v_ETA1_RANDOMNESS_SIZE):array u8 v_ETA1_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
          in
          let error:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution (Rust_primitives.unsize prf_output

                <:
                slice u8)
          in
          let error_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at error_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_representation error
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, error_as_ntt, prf_input)
  in
  let tt_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Ntt.multiply_matrix_by_column v_A_transpose secret_as_ntt
  in
  let tt_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      tt_as_ntt
      (fun tt_as_ntt i ->
          Rust_primitives.Hax.update_at tt_as_ntt
            i
            ((tt_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) +!
              (error_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
              <:
              (Libcrux.Kem.Kyber.Arithmetic.impl_3).f_Output)
          <:
          array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
  in
  let public_key_serialized:Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.impl__new (Rust_primitives.Hax.repeat 0uy v_PUBLIC_KEY_SIZE
        <:
        array u8 v_PUBLIC_KEY_SIZE)
  in
  let public_key_serialized:Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.f_push public_key_serialized
      (Rust_primitives.unsize (encode_12_ tt_as_ntt <: array u8 v_BYTES_PER_RING_ELEMENT)
        <:
        slice u8)
  in
  let public_key_serialized:array u8 v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.impl__array (Libcrux.Kem.Kyber.Conversions.f_push public_key_serialized
          seed_for_A
        <:
        Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE)
  in
  let secret_key_serialized:array u8 v_PRIVATE_KEY_SIZE = encode_12_ secret_as_ntt in
  FStar.Pervasives.Native.Mktuple2 (Core.Convert.f_into secret_key_serialized)
    (Core.Convert.f_into public_key_serialized),
  sampling_A_error

let serialize_secret_key
      (#v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: slice u8)
    : array u8 v_SERIALIZED_KEY_LEN =
  Libcrux.Kem.Kyber.Conversions.impl__array (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.f_push
            (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.impl__new
                        (Rust_primitives.Hax.repeat 0uy v_SERIALIZED_KEY_LEN
                          <:
                          array u8 v_SERIALIZED_KEY_LEN)
                      <:
                      Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)
                    private_key
                  <:
                  Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)
                public_key
              <:
              Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)
            (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H public_key
                  <:
                  array u8 (sz 32))
              <:
              slice u8)
          <:
          Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)
        implicit_rejection_value
      <:
      Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)

let compress_then_encode_u
      (#v_K #v_OUT_LEN #v_COMPRESSION_FACTOR #v_BLOCK_LEN: usize)
      (input: array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : array u8 v_OUT_LEN =
  let out:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let out:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Iter.Traits.Collect.f_into_iter input
                <:
                (Core.Array.Iter.impl Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
                  .f_IntoIter)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                v_K))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                v_K)))
          .f_IntoIter)
      out
      (fun out (i, re) ->
          Rust_primitives.Hax.update_at out
            ({
                Core.Ops.Range.f_start = i *! (v_OUT_LEN /! v_K <: usize) <: usize;
                Core.Ops.Range.f_end = (i +! sz 1 <: usize) *! (v_OUT_LEN /! v_K <: usize) <: usize
              })
            (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut out
                    ({
                        Core.Ops.Range.f_start = i *! (v_OUT_LEN /! v_K <: usize) <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! sz 1 <: usize) *! (v_OUT_LEN /! v_K <: usize) <: usize
                      })
                  <:
                  slice u8)
                (Rust_primitives.unsize (Libcrux.Kem.Kyber.Serialize.serialize_little_endian (Libcrux.Kem.Kyber.Compress.compress
                            re
                          <:
                          Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                      <:
                      array u8 v_BLOCK_LEN)
                  <:
                  slice u8)
              <:
              slice u8)
          <:
          array u8 v_OUT_LEN)
  in
  out

let encrypt
      (#v_K #v_CIPHERTEXT_SIZE #v_T_AS_NTT_ENCODED_SIZE #v_C1_LEN #v_C2_LEN #v_VECTOR_U_COMPRESSION_FACTOR #v_VECTOR_V_COMPRESSION_FACTOR #v_BLOCK_LEN #v_ETA1 #v_ETA1_RANDOMNESS_SIZE #v_ETA2 #v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: slice u8)
      (message: array u8 (sz 32))
      (randomness: slice u8)
    : (Libcrux.Kem.Kyber.t_KyberCiphertext v_CIPHERTEXT_SIZE &
      Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
  let tt_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__ZERO v_K
  in
  let tt_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (public_key.[ {
                        Core.Ops.Range.f_end = v_T_AS_NTT_ENCODED_SIZE
                      } ]
                    <:
                    slice u8)
                  Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8)))
          .f_IntoIter)
      tt_as_ntt
      (fun tt_as_ntt (i, tt_as_ntt_bytes) ->
          Rust_primitives.Hax.update_at tt_as_ntt
            i
            (Libcrux.Kem.Kyber.Serialize.deserialize_little_endian tt_as_ntt_bytes
              <:
              Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          <:
          array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
  in
  let seed:slice u8 = public_key.[ { Core.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE } ] in
  let v_A_transpose, sampling_A_error:(array
      (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
    sample_matrix_A (Libcrux.Kem.Kyber.Conversions.into_padded_array seed <: array u8 (sz 34)) false
  in
  let (prf_input: array u8 (sz 33)):array u8 (sz 33) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array randomness
  in
  let r_as_ntt, domain_separator:(array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
      v_K &
    u8) =
    cbd prf_input
  in
  let error_1_:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__ZERO v_K
  in
  let domain_separator, error_1_, prf_input:(u8 &
    array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K &
    array u8 (sz 33)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (domain_separator, error_1_, prf_input)
      (fun (domain_separator, error_1_, prf_input) i ->
          let prf_input:array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: array u8 v_ETA2_RANDOMNESS_SIZE):array u8 v_ETA2_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
          in
          let error_1_:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at error_1_
              i
              (Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution (Rust_primitives.unsize prf_output

                    <:
                    slice u8)
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, error_1_, prf_input)
  in
  let prf_input:array u8 (sz 33) =
    Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
  in
  let (prf_output: array u8 v_ETA2_RANDOMNESS_SIZE):array u8 v_ETA2_RANDOMNESS_SIZE =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
  in
  let error_2_:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution (Rust_primitives.unsize prf_output
        <:
        slice u8)
  in
  let u:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Ntt.multiply_matrix_by_column_montgomery v_A_transpose r_as_ntt
  in
  let u:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      u
      (fun u i ->
          Rust_primitives.Hax.update_at u
            i
            ((Libcrux.Kem.Kyber.Ntt.invert_ntt_montgomery (u.[ i ]
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) +!
              (error_1_.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
              <:
              (Libcrux.Kem.Kyber.Arithmetic.impl_3).f_Output)
          <:
          array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
  in
  let message_as_ring_element:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Serialize.deserialize_little_endian (Rust_primitives.unsize message
        <:
        slice u8)
  in
  let v =
    ((Libcrux.Kem.Kyber.Ntt.invert_ntt_montgomery (Libcrux.Kem.Kyber.Ntt.multiply_row_by_column_montgomery
              tt_as_ntt
              r_as_ntt
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
        <:
        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) +!
      error_2_
      <:
      (Libcrux.Kem.Kyber.Arithmetic.impl_3).f_Output) +!
    (Libcrux.Kem.Kyber.Compress.decompress message_as_ring_element
      <:
      Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
  in
  let c1:array u8 v_C1_LEN = compress_then_encode_u u in
  let c2:array u8 v_C2_LEN =
    Libcrux.Kem.Kyber.Serialize.serialize_little_endian (Libcrux.Kem.Kyber.Compress.compress v
        <:
        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
  in
  let (ciphertext: array u8 v_CIPHERTEXT_SIZE):array u8 v_CIPHERTEXT_SIZE =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (Rust_primitives.unsize c1 <: slice u8)
  in
  let ciphertext:array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.update_at ciphertext
      ({ Core.Ops.Range.f_start = v_C1_LEN })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut ciphertext
              ({ Core.Ops.Range.f_start = v_C1_LEN })
            <:
            slice u8)
          (Core.Array.impl_23__as_slice c2 <: slice u8)
        <:
        slice u8)
  in
  Core.Convert.f_into ciphertext, sampling_A_error

let decrypt
      (#v_K #v_CIPHERTEXT_SIZE #v_VECTOR_U_ENCODED_SIZE #v_VECTOR_U_COMPRESSION_FACTOR #v_VECTOR_V_COMPRESSION_FACTOR:
          usize)
      (secret_key: slice u8)
      (ciphertext: Libcrux.Kem.Kyber.t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : array u8 (sz 32) =
  let u_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__ZERO v_K
  in
  let secret_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__ZERO v_K
  in
  let u_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (ciphertext.[ {
                        Core.Ops.Range.f_end = v_VECTOR_U_ENCODED_SIZE
                      } ]
                    <:
                    slice u8)
                  ((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
                      v_VECTOR_U_COMPRESSION_FACTOR
                      <:
                      usize) /!
                    sz 8
                    <:
                    usize)
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8)))
          .f_IntoIter)
      u_as_ntt
      (fun u_as_ntt (i, u_bytes) ->
          let u:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Compress.decompress (Libcrux.Kem.Kyber.Serialize.deserialize_little_endian
                  u_bytes
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          let u_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at u_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_representation u
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          u_as_ntt)
  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Compress.decompress (Libcrux.Kem.Kyber.Serialize.deserialize_little_endian (ciphertext.[
              { Core.Ops.Range.f_start = v_VECTOR_U_ENCODED_SIZE } ]
            <:
            slice u8)
        <:
        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
  in
  let secret_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact secret_key
                  Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8)))
          .f_IntoIter)
      secret_as_ntt
      (fun secret_as_ntt (i, secret_bytes) ->
          Rust_primitives.Hax.update_at secret_as_ntt
            i
            (Libcrux.Kem.Kyber.Serialize.deserialize_little_endian secret_bytes
              <:
              Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          <:
          array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
  in
  let message =
    v -!
    (Libcrux.Kem.Kyber.Ntt.invert_ntt_montgomery (Libcrux.Kem.Kyber.Ntt.multiply_row_by_column_montgomery
            secret_as_ntt
            u_as_ntt
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
      <:
      Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
  in
  Libcrux.Kem.Kyber.Serialize.serialize_little_endian (Libcrux.Kem.Kyber.Compress.compress message
      <:
      Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)