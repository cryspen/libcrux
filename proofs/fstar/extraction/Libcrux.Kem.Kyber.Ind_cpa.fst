module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let serialize_secret_key
      (#v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : t_Array u8 v_SERIALIZED_KEY_LEN =
  Libcrux.Kem.Kyber.Conversions.impl__array (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.f_push
            (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.impl__new
                        (Rust_primitives.Hax.repeat 0uy v_SERIALIZED_KEY_LEN
                          <:
                          t_Array u8 v_SERIALIZED_KEY_LEN)
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
                  t_Array u8 (sz 32))
              <:
              t_Slice u8)
          <:
          Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)
        implicit_rejection_value
      <:
      Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)

let sample_matrix_A (#v_K: usize) (seed: t_Array u8 (sz 34)) (transpose: bool)
    : (t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let v_A_transpose:t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
          v_K
        <:
        t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
      v_K
  in
  let sampling_A_error:Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error =
    Core.Option.Option_None
  in
  let v_A_transpose, sampling_A_error:(t_Array
      (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        Core.Ops.Range.t_Range usize)
      (v_A_transpose, sampling_A_error)
      (fun (v_A_transpose, sampling_A_error) i ->
          let seeds:t_Array (t_Array u8 (sz 34)) v_K = Rust_primitives.Hax.repeat seed v_K in
          let seeds:t_Array (t_Array u8 (sz 34)) v_K =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = sz 0;
                      Core.Ops.Range.f_end = v_K
                    })
                <:
                Core.Ops.Range.t_Range usize)
              seeds
              (fun seeds j ->
                  let seeds:t_Array (t_Array u8 (sz 34)) v_K =
                    Rust_primitives.Hax.update_at seeds
                      j
                      (Rust_primitives.Hax.update_at (seeds.[ j ] <: t_Array u8 (sz 34))
                          (sz 32)
                          (cast i <: u8)
                        <:
                        t_Array u8 (sz 34))
                  in
                  let seeds:t_Array (t_Array u8 (sz 34)) v_K =
                    Rust_primitives.Hax.update_at seeds
                      j
                      (Rust_primitives.Hax.update_at (seeds.[ j ] <: t_Array u8 (sz 34))
                          (sz 33)
                          (cast j <: u8)
                        <:
                        t_Array u8 (sz 34))
                  in
                  seeds)
          in
          let xof_bytes:t_Array (t_Array u8 (sz 840)) v_K =
            Libcrux.Kem.Kyber.Hash_functions.v_XOFx4 seeds
          in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = v_K
                  })
              <:
              Core.Ops.Range.t_Range usize)
            (v_A_transpose, sampling_A_error)
            (fun (v_A_transpose, sampling_A_error) j ->
                let sampled, error:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
                  Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
                  Libcrux.Kem.Kyber.Sampling.sample_from_uniform_distribution (xof_bytes.[ j ]
                      <:
                      t_Array u8 (sz 840))
                in
                let sampling_A_error:Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error =
                  if Core.Option.impl__is_some error
                  then
                    let sampling_A_error:Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error =
                      error
                    in
                    sampling_A_error
                  else sampling_A_error
                in
                if transpose
                then
                  let v_A_transpose:t_Array
                    (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K =
                    Rust_primitives.Hax.update_at v_A_transpose
                      j
                      (Rust_primitives.Hax.update_at (v_A_transpose.[ j ]
                            <:
                            t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
                          i
                          sampled
                        <:
                        t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
                  in
                  v_A_transpose, sampling_A_error
                else
                  let v_A_transpose:t_Array
                    (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K =
                    Rust_primitives.Hax.update_at v_A_transpose
                      i
                      (Rust_primitives.Hax.update_at (v_A_transpose.[ i ]
                            <:
                            t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
                          j
                          sampled
                        <:
                        t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
                  in
                  v_A_transpose, sampling_A_error))
  in
  v_A_transpose, sampling_A_error

let cbd (#v_K #v_ETA #v_ETA_RANDOMNESS_SIZE: usize) (prf_input: t_Array u8 (sz 33))
    : (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K & u8) =
  let domain_separator:u8 = 0uy in
  let re_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let domain_separator, prf_input, re_as_ntt:(u8 & t_Array u8 (sz 33) &
    t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        Core.Ops.Range.t_Range usize)
      (domain_separator, prf_input, re_as_ntt)
      (fun (domain_separator, prf_input, re_as_ntt) i ->
          let prf_input:t_Array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: t_Array u8 v_ETA_RANDOMNESS_SIZE):t_Array u8 v_ETA_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: t_Slice u8)
          in
          let r:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution (Rust_primitives.unsize prf_output

                <:
                t_Slice u8)
          in
          let re_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at re_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_binomially_sampled_ring_element r
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, prf_input, re_as_ntt)
  in
  re_as_ntt, domain_separator

let serialize_key
      (#v_K #v_OUT_LEN: usize)
      (key: t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : t_Array u8 v_OUT_LEN =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let out:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Iter.Traits.Collect.f_into_iter key
                <:
                Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                  v_K)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                v_K))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K))
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
                  t_Slice u8)
                (Rust_primitives.unsize (Libcrux.Kem.Kyber.Serialize.serialize_uncompressed_ring_element
                        re
                      <:
                      t_Array u8 (sz 384))
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
          <:
          t_Array u8 v_OUT_LEN)
  in
  out

let generate_keypair
      (#v_K #v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE #v_RANKED_BYTES_PER_RING_ELEMENT #v_ETA1 #v_ETA1_RANDOMNESS_SIZE:
          usize)
      (key_generation_seed: t_Slice u8)
    : ((Libcrux.Kem.Kyber.Types.t_PrivateKey v_PRIVATE_KEY_SIZE &
        Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) = Rust_primitives.Hax.repeat 0uy (sz 33) in
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let error_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let (domain_separator: u8):u8 = 0uy in
  let hashed:t_Array u8 (sz 64) = Libcrux.Kem.Kyber.Hash_functions.v_G key_generation_seed in
  let seed_for_A, seed_for_secret_and_error:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8) (sz 32)
  in
  let v_A_transpose, sampling_A_error:(t_Array
      (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
    sample_matrix_A (Libcrux.Kem.Kyber.Conversions.into_padded_array seed_for_A
        <:
        t_Array u8 (sz 34))
      true
  in
  let prf_input:t_Array u8 (sz 33) =
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
            t_Slice u8)
          seed_for_secret_and_error
        <:
        t_Slice u8)
  in
  let domain_separator, prf_input, secret_as_ntt:(u8 & t_Array u8 (sz 33) &
    t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        Core.Ops.Range.t_Range usize)
      (domain_separator, prf_input, secret_as_ntt)
      (fun (domain_separator, prf_input, secret_as_ntt) i ->
          let prf_input:t_Array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: t_Array u8 v_ETA1_RANDOMNESS_SIZE):t_Array u8 v_ETA1_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: t_Slice u8)
          in
          let secret:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution (Rust_primitives.unsize prf_output

                <:
                t_Slice u8)
          in
          let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at secret_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_binomially_sampled_ring_element secret
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, prf_input, secret_as_ntt)
  in
  let domain_separator, error_as_ntt, prf_input:(u8 &
    t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K &
    t_Array u8 (sz 33)) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        Core.Ops.Range.t_Range usize)
      (domain_separator, error_as_ntt, prf_input)
      (fun (domain_separator, error_as_ntt, prf_input) i ->
          let prf_input:t_Array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: t_Array u8 v_ETA1_RANDOMNESS_SIZE):t_Array u8 v_ETA1_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: t_Slice u8)
          in
          let error:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution (Rust_primitives.unsize prf_output

                <:
                t_Slice u8)
          in
          let error_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at error_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_binomially_sampled_ring_element error
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, error_as_ntt, prf_input)
  in
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Ntt.compute_As_plus_e v_A_transpose secret_as_ntt error_as_ntt
  in
  let public_key_serialized:Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.impl__new (Rust_primitives.Hax.repeat 0uy v_PUBLIC_KEY_SIZE
        <:
        t_Array u8 v_PUBLIC_KEY_SIZE)
  in
  let public_key_serialized:Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.f_push public_key_serialized
      (Rust_primitives.unsize (serialize_key tt_as_ntt <: t_Array u8 v_RANKED_BYTES_PER_RING_ELEMENT
          )
        <:
        t_Slice u8)
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.impl__array (Libcrux.Kem.Kyber.Conversions.f_push public_key_serialized
          seed_for_A
        <:
        Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE)
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE = serialize_key secret_as_ntt in
  FStar.Pervasives.Native.Mktuple2 (Core.Convert.f_into secret_key_serialized)
    (Core.Convert.f_into public_key_serialized),
  sampling_A_error

let compress_then_encode_u
      (#v_K #v_OUT_LEN #v_COMPRESSION_FACTOR #v_BLOCK_LEN: usize)
      (input: t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : t_Array u8 v_OUT_LEN =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let out:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Iter.Traits.Collect.f_into_iter input
                <:
                Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                  v_K)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                v_K))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K))
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
                  t_Slice u8)
                (Rust_primitives.unsize (Libcrux.Kem.Kyber.Serialize.serialize_little_endian (Libcrux.Kem.Kyber.Compress.compress
                            re
                          <:
                          Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                      <:
                      t_Array u8 v_BLOCK_LEN)
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
          <:
          t_Array u8 v_OUT_LEN)
  in
  out

let encrypt
      (#v_K #v_CIPHERTEXT_SIZE #v_T_AS_NTT_ENCODED_SIZE #v_C1_LEN #v_C2_LEN #v_VECTOR_U_COMPRESSION_FACTOR #v_VECTOR_V_COMPRESSION_FACTOR #v_BLOCK_LEN #v_ETA1 #v_ETA1_RANDOMNESS_SIZE #v_ETA2 #v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8)
    : (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (public_key.[ {
                        Core.Ops.Range.f_end = v_T_AS_NTT_ENCODED_SIZE
                      } ]
                    <:
                    t_Slice u8)
                  Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      tt_as_ntt
      (fun tt_as_ntt (i, tt_as_ntt_bytes) ->
          Rust_primitives.Hax.update_at tt_as_ntt
            i
            (Libcrux.Kem.Kyber.Serialize.deserialize_to_uncompressed_ring_element tt_as_ntt_bytes
              <:
              Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          <:
          t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
  in
  let seed:t_Slice u8 = public_key.[ { Core.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE } ] in
  let v_A_transpose, sampling_A_error:(t_Array
      (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
    sample_matrix_A (Libcrux.Kem.Kyber.Conversions.into_padded_array seed <: t_Array u8 (sz 34))
      false
  in
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array randomness
  in
  let r_as_ntt, domain_separator:(t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
      v_K &
    u8) =
    cbd prf_input
  in
  let error_1_:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let domain_separator, error_1_, prf_input:(u8 &
    t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K &
    t_Array u8 (sz 33)) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        Core.Ops.Range.t_Range usize)
      (domain_separator, error_1_, prf_input)
      (fun (domain_separator, error_1_, prf_input) i ->
          let prf_input:t_Array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: t_Array u8 v_ETA2_RANDOMNESS_SIZE):t_Array u8 v_ETA2_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: t_Slice u8)
          in
          let error_1_:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at error_1_
              i
              (Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution (Rust_primitives.unsize prf_output

                    <:
                    t_Slice u8)
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, error_1_, prf_input)
  in
  let prf_input:t_Array u8 (sz 33) =
    Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
  in
  let (prf_output: t_Array u8 v_ETA2_RANDOMNESS_SIZE):t_Array u8 v_ETA2_RANDOMNESS_SIZE =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: t_Slice u8)
  in
  let error_2_:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution (Rust_primitives.unsize prf_output
        <:
        t_Slice u8)
  in
  let u:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Ntt.compute_vector_u v_A_transpose r_as_ntt error_1_
  in
  let message_as_ring_element:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Serialize.deserialize_then_decompress_message message
  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Ntt.compute_ring_element_v tt_as_ntt r_as_ntt error_2_ message_as_ring_element
  in
  let c1:t_Array u8 v_C1_LEN = compress_then_encode_u u in
  let c2:t_Array u8 v_C2_LEN =
    Libcrux.Kem.Kyber.Serialize.serialize_little_endian (Libcrux.Kem.Kyber.Compress.compress v
        <:
        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
  in
  let (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE):t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (Rust_primitives.unsize c1 <: t_Slice u8)
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.update_at ciphertext
      ({ Core.Ops.Range.f_start = v_C1_LEN })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut ciphertext
              ({ Core.Ops.Range.f_start = v_C1_LEN })
            <:
            t_Slice u8)
          (Core.Array.impl_23__as_slice c2 <: t_Slice u8)
        <:
        t_Slice u8)
  in
  Core.Convert.f_into ciphertext, sampling_A_error

let decrypt
      (#v_K #v_CIPHERTEXT_SIZE #v_VECTOR_U_ENCODED_SIZE #v_VECTOR_U_COMPRESSION_FACTOR #v_VECTOR_V_COMPRESSION_FACTOR:
          usize)
      (secret_key: t_Slice u8)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : t_Array u8 (sz 32) =
  let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (ciphertext.[ {
                        Core.Ops.Range.f_end = v_VECTOR_U_ENCODED_SIZE
                      } ]
                    <:
                    t_Slice u8)
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
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      u_as_ntt
      (fun u_as_ntt (i, u_bytes) ->
          let u:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Compress.decompress (Libcrux.Kem.Kyber.Serialize.deserialize_little_endian
                  u_bytes
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at u_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_vector_u u
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          u_as_ntt)
  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Compress.decompress (Libcrux.Kem.Kyber.Serialize.deserialize_little_endian (ciphertext.[
              { Core.Ops.Range.f_start = v_VECTOR_U_ENCODED_SIZE } ]
            <:
            t_Slice u8)
        <:
        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
  in
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact secret_key
                  Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      secret_as_ntt
      (fun secret_as_ntt (i, secret_bytes) ->
          Rust_primitives.Hax.update_at secret_as_ntt
            i
            (Libcrux.Kem.Kyber.Serialize.deserialize_to_uncompressed_ring_element secret_bytes
              <:
              Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          <:
          t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
  in
  let message:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Ntt.compute_message v secret_as_ntt u_as_ntt
  in
  Libcrux.Kem.Kyber.Serialize.compress_then_serialize_message message