module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_PrivateKey = { f_value:array u8 v_SIZE }

let impl (#size: usize) : Core.Convert.t_AsRef (t_PrivateKey v_SIZE) (slice u8) =
  {
    as_ref
    =
    fun (#size: usize) (self: t_PrivateKey v_SIZE) ->
      Rust_primitives.unsize self.Libcrux.Kem.Kyber.Ind_cpa.PrivateKey.f_value
  }

let impl (#size: usize) : Core.Convert.t_From (t_PrivateKey v_SIZE) (array u8 v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: array u8 v_SIZE) ->
      { Libcrux.Kem.Kyber.Ind_cpa.PrivateKey.f_value = value }
  }

let impl (#size: usize) : Core.Convert.t_From (array u8 v_SIZE) (t_PrivateKey v_SIZE) =
  {
    from
    =
    fun (#size: usize) (value: t_PrivateKey v_SIZE) ->
      value.Libcrux.Kem.Kyber.Ind_cpa.PrivateKey.f_value
  }

let impl (#size: usize) : Core.Convert.t_TryFrom (t_PrivateKey v_SIZE) (slice u8) =
  {
    error = Core.Array.t_TryFromSliceError;
    try_from
    =
    fun (#size: usize) (value: slice u8) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist2:array u8 v_SIZE =
            match
              Core.Ops.Try_trait.Try.branch (Core.Convert.TryInto.try_into value
                  <:
                  Core.Result.t_Result (array u8 v_SIZE) _)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist1:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                      residual
                    <:
                    Core.Result.t_Result (t_PrivateKey v_SIZE) Core.Array.t_TryFromSliceError)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist1)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist3:t_PrivateKey v_SIZE =
              { Libcrux.Kem.Kyber.Ind_cpa.PrivateKey.f_value = hoist2 }
            in
            Core.Result.Result_Ok hoist3))
  }

let impl (#size: usize) : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) usize =
  {
    output = u8;
    index
    =
    fun (#size: usize) (self: t_PrivateKey v_SIZE) (index: usize) ->
      self.Libcrux.Kem.Kyber.Ind_cpa.PrivateKey.f_value.[ index ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) (Core.Ops.Range.t_Range usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_PrivateKey v_SIZE) (range: Core.Ops.Range.t_Range usize) ->
      self.Libcrux.Kem.Kyber.Ind_cpa.PrivateKey.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) (Core.Ops.Range.t_RangeTo usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_PrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeTo usize) ->
      self.Libcrux.Kem.Kyber.Ind_cpa.PrivateKey.f_value.[ range ]
  }

let impl (#size: usize)
    : Core.Ops.Index.t_Index (t_PrivateKey v_SIZE) (Core.Ops.Range.t_RangeFrom usize) =
  {
    output = slice u8;
    index
    =
    fun (#size: usize) (self: t_PrivateKey v_SIZE) (range: Core.Ops.Range.t_RangeFrom usize) ->
      self.Libcrux.Kem.Kyber.Ind_cpa.PrivateKey.f_value.[ range ]
  }

let as_slice_under_impl_8 (#size: usize) (self: t_PrivateKey v_SIZE) : array u8 v_SIZE =
  self.Libcrux.Kem.Kyber.Ind_cpa.PrivateKey.f_value

let split_at_under_impl_8 (#size: usize) (self: t_PrivateKey v_SIZE) (mid: usize)
    : (slice u8 & slice u8) =
  Core.Slice.split_at_under_impl (Rust_primitives.unsize self
          .Libcrux.Kem.Kyber.Ind_cpa.PrivateKey.f_value
      <:
      slice u8)
    mid

let len_under_impl_8 (#size: usize) (self: t_PrivateKey v_SIZE) : usize = v_SIZE

let sample_matrix_A (#k: usize) (seed: array u8 34sz) (transpose: bool)
    : (array (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
      Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
  let v_A_transpose:array (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K
  =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
          v_K
        <:
        array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
      v_K
  in
  let sampling_A_error:Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError
  =
    Core.Option.Option_None
  in
  let v_A_transpose, sampling_A_error, seed:(array
      (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError &
    array u8 34sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K
            })
        <:
        _)
      (v_A_transpose, sampling_A_error, seed)
      (fun (v_A_transpose, sampling_A_error, seed) i ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = v_K
                  })
              <:
              _)
            (v_A_transpose, sampling_A_error, seed)
            (fun (v_A_transpose, sampling_A_error, seed) j ->
                let seed:array u8 34sz = Rust_primitives.Hax.update_at seed 32sz (cast i) in
                let seed:array u8 34sz = Rust_primitives.Hax.update_at seed 33sz (cast j) in
                let (xof_bytes: array u8 840sz):array u8 840sz =
                  Libcrux.Kem.Kyber.Hash_functions.v_XOF (Rust_primitives.unsize seed <: slice u8)
                in
                let sampled, error:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
                  Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
                  Libcrux.Kem.Kyber.Sampling.sample_from_uniform_distribution xof_bytes
                in
                let sampling_A_error:Core.Option.t_Option
                Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
                  if Core.Option.is_some_under_impl error
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
                  v_A_transpose, sampling_A_error, seed
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
                  v_A_transpose, sampling_A_error, seed)
          <:
          (array (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
            Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError &
            array u8 34sz))
  in
  v_A_transpose, sampling_A_error

let cbd (#k: usize) (prf_input: array u8 33sz)
    : (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K & u8) =
  let domain_separator:u8 = 0uy in
  let re_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl v_K
  in
  let domain_separator, prf_input, re_as_ntt:(Prims.unit & array u8 33sz &
    array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K
            })
        <:
        _)
      (domain_separator, prf_input, re_as_ntt)
      (fun (domain_separator, prf_input, re_as_ntt) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
          in
          let r:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution_2_ prf_output
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
      (#k #out_len: usize)
      (input: array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : array u8 v_OUT_LEN =
  let out:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let out:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Iter.Traits.Collect.IntoIterator.into_iter input <: _)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                v_K))
        <:
        _)
      out
      (fun out (i, re) ->
          Rust_primitives.Hax.update_at out
            ({
                Core.Ops.Range.Range.f_start
                =
                i *. Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                Core.Ops.Range.Range.f_end
                =
                (i +. 1sz <: usize) *. Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize
              })
            (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut out
                    ({
                        Core.Ops.Range.Range.f_start
                        =
                        i *. Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                        Core.Ops.Range.Range.f_end
                        =
                        (i +. 1sz <: usize) *. Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                        <:
                        usize
                      })
                  <:
                  slice u8)
                (Rust_primitives.unsize (Libcrux.Kem.Kyber.Serialize.serialize_little_endian re
                      <:
                      array u8 384sz)
                  <:
                  slice u8)
              <:
              slice u8)
          <:
          array u8 v_OUT_LEN)
  in
  out

let generate_keypair
      (#k #private_key_size #public_key_size #bytes_per_ring_element: usize)
      (key_generation_seed: slice u8)
    : ((t_PrivateKey v_PRIVATE_KEY_SIZE & Libcrux.Kem.Kyber.t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
      Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
  let (prf_input: array u8 33sz):array u8 33sz = Rust_primitives.Hax.repeat 0uy 33sz in
  let secret_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl v_K
  in
  let error_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl v_K
  in
  let (domain_separator: u8):u8 = 0uy in
  let hashed:array u8 64sz = Libcrux.Kem.Kyber.Hash_functions.v_G key_generation_seed in
  let seed_for_A, seed_for_secret_and_error:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8) 32sz
  in
  let v_A_transpose, sampling_A_error:(array
      (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
    sample_matrix_A (Libcrux.Kem.Kyber.Conversions.into_padded_array seed_for_A <: array u8 34sz)
      true
  in
  let prf_input:array u8 33sz =
    Rust_primitives.Hax.update_at prf_input
      ({
          Core.Ops.Range.Range.f_start = 0sz;
          Core.Ops.Range.Range.f_end = Core.Slice.len_under_impl seed_for_secret_and_error <: usize
        })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut prf_input
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Core.Slice.len_under_impl seed_for_secret_and_error <: usize
                })
            <:
            slice u8)
          seed_for_secret_and_error
        <:
        slice u8)
  in
  let domain_separator, prf_input, secret_as_ntt:(Prims.unit & array u8 33sz &
    array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K
            })
        <:
        _)
      (domain_separator, prf_input, secret_as_ntt)
      (fun (domain_separator, prf_input, secret_as_ntt) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
          in
          let secret:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution_2_ prf_output
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
  let domain_separator, error_as_ntt, prf_input:(Prims.unit &
    array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K &
    array u8 33sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K
            })
        <:
        _)
      (domain_separator, error_as_ntt, prf_input)
      (fun (domain_separator, error_as_ntt, prf_input) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
          in
          let error:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution_2_ prf_output
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
  let t__as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Ntt.multiply_matrix_by_column v_A_transpose secret_as_ntt
  in
  let t__as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K
            })
        <:
        _)
      t__as_ntt
      (fun t__as_ntt i ->
          Rust_primitives.Hax.update_at t__as_ntt
            i
            ((t__as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) +.
              (error_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
              <:
              _)
          <:
          array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
  in
  let public_key_serialized:Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.new_under_impl (Rust_primitives.Hax.repeat 0uy v_PUBLIC_KEY_SIZE
        <:
        array u8 v_PUBLIC_KEY_SIZE)
  in
  let public_key_serialized:Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.UpdatingArray.push public_key_serialized
      (Rust_primitives.unsize (encode_12_ t__as_ntt <: array u8 v_BYTES_PER_RING_ELEMENT)
        <:
        slice u8)
  in
  let public_key_serialized:array u8 v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.array_under_impl (Libcrux.Kem.Kyber.Conversions.UpdatingArray.push
          public_key_serialized
          seed_for_A
        <:
        Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE)
  in
  let secret_key_serialized:array u8 v_PRIVATE_KEY_SIZE = encode_12_ secret_as_ntt in
  FStar.Pervasives.Native.Mktuple2 (Core.Convert.Into.into secret_key_serialized)
    (Core.Convert.Into.into public_key_serialized),
  sampling_A_error

let serialize_secret_key
      (#serialized_key_len: usize)
      (private_key public_key implicit_rejection_value: slice u8)
    : array u8 v_SERIALIZED_KEY_LEN =
  Libcrux.Kem.Kyber.Conversions.array_under_impl (Libcrux.Kem.Kyber.Conversions.UpdatingArray.push (Libcrux.Kem.Kyber.Conversions.UpdatingArray.push
            (Libcrux.Kem.Kyber.Conversions.UpdatingArray.push (Libcrux.Kem.Kyber.Conversions.UpdatingArray.push
                    (Libcrux.Kem.Kyber.Conversions.new_under_impl (Rust_primitives.Hax.repeat 0uy
                            v_SERIALIZED_KEY_LEN
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
                  array u8 32sz)
              <:
              slice u8)
          <:
          Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)
        implicit_rejection_value
      <:
      Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)

let compress_then_encode_u
      (#k #out_len #compression_factor #block_len: usize)
      (input: array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : array u8 v_OUT_LEN =
  let out:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let out:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Iter.Traits.Collect.IntoIterator.into_iter input <: _)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                v_K))
        <:
        _)
      out
      (fun out (i, re) ->
          Rust_primitives.Hax.update_at out
            ({
                Core.Ops.Range.Range.f_start = i *. (v_OUT_LEN /. v_K <: usize) <: usize;
                Core.Ops.Range.Range.f_end
                =
                (i +. 1sz <: usize) *. (v_OUT_LEN /. v_K <: usize) <: usize
              })
            (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut out
                    ({
                        Core.Ops.Range.Range.f_start = i *. (v_OUT_LEN /. v_K <: usize) <: usize;
                        Core.Ops.Range.Range.f_end
                        =
                        (i +. 1sz <: usize) *. (v_OUT_LEN /. v_K <: usize) <: usize
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
      (#k #ciphertext_size #t__as_ntt_encoded_size #c1_len #c2_len #vector_u_compression_factor #vector_v_compression_factor #block_len:
          usize)
      (public_key: slice u8)
      (message: array u8 32sz)
      (randomness: slice u8)
    : (Libcrux.Kem.Kyber.t_KyberCiphertext v_CIPHERTEXT_SIZE &
      Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
  let t__as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl v_K
  in
  let t__as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (public_key.[ {
                        Core.Ops.Range.RangeTo.f_end = v_T_AS_NTT_ENCODED_SIZE
                      } ]
                    <:
                    slice u8)
                  Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      t__as_ntt
      (fun t__as_ntt (i, t__as_ntt_bytes) ->
          Rust_primitives.Hax.update_at t__as_ntt
            i
            (Libcrux.Kem.Kyber.Serialize.deserialize_little_endian t__as_ntt_bytes
              <:
              Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          <:
          array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
  in
  let seed:slice u8 =
    public_key.[ { Core.Ops.Range.RangeFrom.f_start = v_T_AS_NTT_ENCODED_SIZE } ]
  in
  let v_A_transpose, sampling_A_error:(array
      (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
    sample_matrix_A (Libcrux.Kem.Kyber.Conversions.into_padded_array seed <: array u8 34sz) false
  in
  let (prf_input: array u8 33sz):array u8 33sz =
    Libcrux.Kem.Kyber.Conversions.into_padded_array randomness
  in
  let r_as_ntt, domain_separator:(array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
      v_K &
    u8) =
    cbd prf_input
  in
  let error_1_:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl v_K
  in
  let domain_separator, error_1_, prf_input:(Prims.unit &
    array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K &
    array u8 33sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K
            })
        <:
        _)
      (domain_separator, error_1_, prf_input)
      (fun (domain_separator, error_1_, prf_input) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
          in
          let error_1_:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at error_1_
              i
              (Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution_2_ prf_output
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, error_1_, prf_input)
  in
  let prf_input:array u8 33sz = Rust_primitives.Hax.update_at prf_input 32sz domain_separator in
  let (prf_output: array u8 128sz):array u8 128sz =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
  in
  let error_2_:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution_2_ prf_output
  in
  let u:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Ntt.multiply_matrix_by_column_montgomery v_A_transpose r_as_ntt
  in
  let u:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K
            })
        <:
        _)
      u
      (fun u i ->
          Rust_primitives.Hax.update_at u
            i
            ((Libcrux.Kem.Kyber.Ntt.invert_ntt_montgomery (u.[ i ]
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) +.
              (error_1_.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
              <:
              _)
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
              t__as_ntt
              r_as_ntt
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
        <:
        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) +.
      error_2_
      <:
      _) +.
    (Libcrux.Kem.Kyber.Compress.decompress message_as_ring_element 1sz
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
      ({ Core.Ops.Range.RangeFrom.f_start = v_C1_LEN })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut ciphertext
              ({ Core.Ops.Range.RangeFrom.f_start = v_C1_LEN })
            <:
            slice u8)
          (Core.Array.as_slice_under_impl_23 c2 <: slice u8)
        <:
        slice u8)
  in
  Core.Convert.Into.into ciphertext, sampling_A_error

let decrypt
      (#k #ciphertext_size #vector_u_encoded_size #vector_u_compression_factor #vector_v_compression_factor:
          usize)
      (secret_key: slice u8)
      (ciphertext: Libcrux.Kem.Kyber.t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : array u8 32sz =
  let u_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl v_K
  in
  let secret_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl v_K
  in
  let u_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (ciphertext.[ {
                        Core.Ops.Range.RangeTo.f_end = v_VECTOR_U_ENCODED_SIZE
                      } ]
                    <:
                    slice u8)
                  ((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *.
                      v_VECTOR_U_COMPRESSION_FACTOR
                      <:
                      usize) /.
                    8sz
                    <:
                    usize)
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      u_as_ntt
      (fun u_as_ntt (i, u_bytes) ->
          let u:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Serialize.deserialize_little_endian u_bytes
          in
          let u_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at u_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_representation (Libcrux.Kem.Kyber.Compress.decompress u
                      10sz
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          u_as_ntt)
  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Compress.decompress (Libcrux.Kem.Kyber.Serialize.deserialize_little_endian (ciphertext.[
              { Core.Ops.Range.RangeFrom.f_start = v_VECTOR_U_ENCODED_SIZE } ]
            <:
            slice u8)
        <:
        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
      v_VECTOR_V_COMPRESSION_FACTOR
  in
  let secret_as_ntt:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl secret_key
                  Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
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
    v -.
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