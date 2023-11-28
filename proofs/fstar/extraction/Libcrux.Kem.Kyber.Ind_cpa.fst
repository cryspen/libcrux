module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let update_domain_separator (value: u8) : FStar.HyperStack.ST.St Prims.unit =
  let value:u8 = value +! 1uy in
  ()

let serialize_secret_key
      (v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : FStar.HyperStack.ST.St (t_Array u8 v_SERIALIZED_KEY_LEN) =
  Libcrux.Kem.Kyber.Conversions.impl__array v_SERIALIZED_KEY_LEN
    (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.f_push
                (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.impl__new v_SERIALIZED_KEY_LEN
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

let sample_vector_cbd_then_ntt
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : FStar.HyperStack.ST.St (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) =
  let re_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      v_K
      (fun i ->
          let i:usize = i in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize prf_input
              (sz 32)
              domain_separator
          in
          let _:Prims.unit = update_domain_separator domain_separator in
          let (prf_output: t_Array u8 v_ETA_RANDOMNESS_SIZE):t_Array u8 v_ETA_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF v_ETA_RANDOMNESS_SIZE
              (Rust_primitives.unsize prf_input <: t_Slice u8)
          in
          let r:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution v_ETA
              (Rust_primitives.unsize prf_output <: t_Slice u8)
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize re_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_binomially_sampled_ring_element r
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          ())
  in
  re_as_ntt

let sample_matrix_A (v_K: usize) (seed: t_Array u8 (sz 34)) (transpose: bool)
    : FStar.HyperStack.ST.St
    (t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let v_A_transpose:t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
          v_K
        <:
        t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      v_K
  in
  let sampling_error:Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error =
    Core.Option.Option_None <: Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      v_K
      (fun i ->
          let i:usize = i in
          let seeds:t_Array (t_Array u8 (sz 34)) v_K = Rust_primitives.Hax.repeat seed v_K in
          let _:Prims.unit =
            Rust_primitives.f_for_loop (sz 0)
              v_K
              (fun j ->
                  let j:usize = j in
                  let _:Prims.unit =
                    Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize (seeds.[ j ]
                        <:
                        t_Array u8 (sz 34))
                      (sz 32)
                      (cast (i <: usize) <: u8)
                  in
                  let _:Prims.unit =
                    Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize (seeds.[ j ]
                        <:
                        t_Array u8 (sz 34))
                      (sz 33)
                      (cast (j <: usize) <: u8)
                  in
                  ())
          in
          let xof_bytes:t_Array (t_Array u8 (sz 840)) v_K =
            Libcrux.Kem.Kyber.Hash_functions.v_XOFx4 (sz 840) v_K seeds
          in
          Rust_primitives.f_for_loop (sz 0)
            v_K
            (fun j ->
                let j:usize = j in
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                  Libcrux.Kem.Kyber.Sampling.sample_from_uniform_distribution (sz 840)
                    (xof_bytes.[ j ] <: t_Array u8 (sz 840))
                    sampling_error
                in
                if transpose
                then
                  let _:Prims.unit =
                    Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize (v_A_transpose.[
                          j ]
                        <:
                        t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
                      i
                      sampled
                  in
                  ()
                else
                  let _:Prims.unit =
                    Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize (v_A_transpose.[
                          i ]
                        <:
                        t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
                      j
                      sampled
                  in
                  ()))
  in
  v_A_transpose, sampling_error
  <:
  (t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)

let compress_then_encode_u
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (input: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : FStar.HyperStack.ST.St (t_Array u8 v_OUT_LEN) =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (Core.Slice.impl__len (Rust_primitives.unsize input
            <:
            t_Slice Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
        <:
        usize)
      (fun i ->
          let i:usize = i in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = input.[ i ] in
          let _:Prims.unit =
            Core.Slice.impl__copy_from_slice (Core.Ops.Index.f_index_mut out
                  ({
                      Core.Ops.Range.f_start = i *! (v_OUT_LEN /! v_K <: usize) <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! sz 1 <: usize) *! (v_OUT_LEN /! v_K <: usize) <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                t_Slice u8)
              (Rust_primitives.unsize (Libcrux.Kem.Kyber.Serialize.compress_then_serialize_ring_element_u
                      v_COMPRESSION_FACTOR
                      v_BLOCK_LEN
                      re
                    <:
                    t_Array u8 v_BLOCK_LEN)
                <:
                t_Slice u8)
          in
          ())
  in
  out

let serialize_key
      (v_K v_OUT_LEN: usize)
      (key: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : FStar.HyperStack.ST.St (t_Array u8 v_OUT_LEN) =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (Core.Slice.impl__len (Rust_primitives.unsize key
            <:
            t_Slice Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
        <:
        usize)
      (fun i ->
          let i:usize = i in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = key.[ i ] in
          let _:Prims.unit =
            Core.Slice.impl__copy_from_slice (Core.Ops.Index.f_index_mut out
                  ({
                      Core.Ops.Range.f_start
                      =
                      i *! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! sz 1 <: usize) *! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                      <:
                      usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                t_Slice u8)
              (Rust_primitives.unsize (Libcrux.Kem.Kyber.Serialize.serialize_uncompressed_ring_element
                      re
                    <:
                    t_Array u8 (sz 384))
                <:
                t_Slice u8)
          in
          ())
  in
  out

let decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (secret_key: t_Slice u8)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : FStar.HyperStack.ST.St (t_Array u8 (sz 32)) =
  let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (v_VECTOR_U_ENCODED_SIZE /!
        ((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_U_COMPRESSION_FACTOR
            <:
            usize) /!
          sz 8
          <:
          usize)
        <:
        usize)
      (fun i ->
          let i:usize = i in
          let outer = (ciphertext.Libcrux.Kem.Kyber.Types.f_value.[ {
                  Core.Ops.Range.f_end = v_VECTOR_U_ENCODED_SIZE
                }
                <:
                Core.Ops.Range.t_RangeTo usize ]
              <:
              t_Slice u8) in
          let u_bytes:t_Slice u8 =
              outer
              .[ {
                Core.Ops.Range.f_start
                =
                i *!
                ((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
                    v_U_COMPRESSION_FACTOR
                    <:
                    usize) /!
                  sz 8
                  <:
                  usize)
                <:
                usize;
                Core.Ops.Range.f_end
                =
                (i *!
                  ((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
                      v_U_COMPRESSION_FACTOR
                      <:
                      usize) /!
                    sz 8
                    <:
                    usize)
                  <:
                  usize) +!
                ((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
                    v_U_COMPRESSION_FACTOR
                    <:
                    usize) /!
                  sz 8
                  <:
                  usize)
                <:
                usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
          in
          let u:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            Libcrux.Kem.Kyber.Serialize.deserialize_then_decompress_ring_element_u v_U_COMPRESSION_FACTOR
              u_bytes
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize u_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_vector_u v_U_COMPRESSION_FACTOR u
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          ())
  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Serialize.deserialize_then_decompress_ring_element_v v_V_COMPRESSION_FACTOR
      (ciphertext.Libcrux.Kem.Kyber.Types.f_value.[ {
            Core.Ops.Range.f_start = v_VECTOR_U_ENCODED_SIZE
          }
          <:
          Core.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      ((Core.Slice.impl__len secret_key <: usize) /!
        Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
        <:
        usize)
      (fun i ->
          let i:usize = i in
          let secret_bytes:t_Slice u8 =
            secret_key.[ {
                Core.Ops.Range.f_start
                =
                i *! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                Core.Ops.Range.f_end
                =
                (i *! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize) +!
                Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize secret_as_ntt
              i
              (Libcrux.Kem.Kyber.Serialize.deserialize_to_uncompressed_ring_element secret_bytes
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          ())
  in
  let message:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Matrix.compute_message v_K v secret_as_ntt u_as_ntt
  in
  Libcrux.Kem.Kyber.Serialize.compress_then_serialize_message message

let encrypt
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8)
    : FStar.HyperStack.ST.St
    (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (v_T_AS_NTT_ENCODED_SIZE /! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize)
      (fun i ->
          let i:usize = i in
          let pk_slice = (public_key.[ { Core.Ops.Range.f_end = v_T_AS_NTT_ENCODED_SIZE }
                <:
                Core.Ops.Range.t_RangeTo usize ]
              <:
              t_Slice u8) in
          let tt_as_ntt_bytes:t_Slice u8 =
            pk_slice.[ {
                Core.Ops.Range.f_start
                =
                i *! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                Core.Ops.Range.f_end
                =
                (i *! Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT <: usize) +!
                Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize tt_as_ntt
              i
              (Libcrux.Kem.Kyber.Serialize.deserialize_to_uncompressed_ring_element tt_as_ntt_bytes
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          ())
  in
  let seed:t_Slice u8 =
    public_key.[ { Core.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE }
      <:
      Core.Ops.Range.t_RangeFrom usize ]
  in
  let v_A_transpose, sampling_A_error:(t_Array
      (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
    sample_matrix_A v_K
      (Libcrux.Kem.Kyber.Conversions.into_padded_array (sz 34) seed <: t_Array u8 (sz 34))
      false
  in
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (sz 33) randomness
  in
  let domain_separator:u8 = 0uy in
  let r_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE prf_input domain_separator
  in
  let error_1_:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      v_K
      (fun i ->
          let i:usize = i in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize prf_input
              (sz 32)
              domain_separator
          in
          let _:Prims.unit = update_domain_separator domain_separator in
          let (prf_output: t_Array u8 v_ETA2_RANDOMNESS_SIZE):t_Array u8 v_ETA2_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF v_ETA2_RANDOMNESS_SIZE
              (Rust_primitives.unsize prf_input <: t_Slice u8)
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize error_1_
              i
              (Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution v_ETA2
                  (Rust_primitives.unsize prf_output <: t_Slice u8)
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          ())
  in
  let _:Prims.unit =
    Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize prf_input
      (sz 32)
      domain_separator
  in
  let (prf_output: t_Array u8 v_ETA2_RANDOMNESS_SIZE):t_Array u8 v_ETA2_RANDOMNESS_SIZE =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF v_ETA2_RANDOMNESS_SIZE
      (Rust_primitives.unsize prf_input <: t_Slice u8)
  in
  let error_2_:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution v_ETA2
      (Rust_primitives.unsize prf_output <: t_Slice u8)
  in
  let u:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Matrix.compute_vector_u v_K v_A_transpose r_as_ntt error_1_
  in
  let message_as_ring_element:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Serialize.deserialize_then_decompress_message message
  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Matrix.compute_ring_element_v v_K
      tt_as_ntt
      r_as_ntt
      error_2_
      message_as_ring_element
  in
  let c1:t_Array u8 v_C1_LEN =
    compress_then_encode_u v_K v_C1_LEN v_U_COMPRESSION_FACTOR v_BLOCK_LEN u
  in
  let c2:t_Array u8 v_C2_LEN =
    Libcrux.Kem.Kyber.Serialize.compress_then_serialize_ring_element_v v_V_COMPRESSION_FACTOR
      v_C2_LEN
      v
  in
  let (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE):t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux.Kem.Kyber.Conversions.into_padded_array v_CIPHERTEXT_SIZE
      (Rust_primitives.unsize c1 <: t_Slice u8)
  in
  Core.Convert.f_into ciphertext, sampling_A_error
  <:
  (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)

let generate_keypair
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (key_generation_seed: t_Slice u8)
    : FStar.HyperStack.ST.St
    ((Libcrux.Kem.Kyber.Types.t_PrivateKey v_PRIVATE_KEY_SIZE &
        Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let hashed:t_Array u8 (sz 64) = Libcrux.Kem.Kyber.Hash_functions.v_G key_generation_seed in
  let seed_for_A, seed_for_secret_and_error:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8) (sz 32)
  in
  let v_A_transpose, sampling_A_error:(t_Array
      (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
    sample_matrix_A v_K
      (Libcrux.Kem.Kyber.Conversions.into_padded_array (sz 34) seed_for_A <: t_Array u8 (sz 34))
      true
  in
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (sz 33) seed_for_secret_and_error
  in
  let domain_separator:u8 = 0uy in
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE prf_input domain_separator
  in
  let error_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE prf_input domain_separator
  in
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Matrix.compute_As_plus_e v_K v_A_transpose secret_as_ntt error_as_ntt
  in
  let public_key_serialized:Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.impl__new v_PUBLIC_KEY_SIZE
      (Rust_primitives.Hax.repeat 0uy v_PUBLIC_KEY_SIZE <: t_Array u8 v_PUBLIC_KEY_SIZE)
  in
  let public_key_serialized:Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.f_push public_key_serialized
      (Rust_primitives.unsize (serialize_key v_K v_RANKED_BYTES_PER_RING_ELEMENT tt_as_ntt
            <:
            t_Array u8 v_RANKED_BYTES_PER_RING_ELEMENT)
        <:
        t_Slice u8)
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.impl__array v_PUBLIC_KEY_SIZE
      (Libcrux.Kem.Kyber.Conversions.f_push public_key_serialized seed_for_A
        <:
        Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE)
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    serialize_key v_K v_PRIVATE_KEY_SIZE secret_as_ntt
  in
  (Core.Convert.f_into secret_key_serialized, Core.Convert.f_into public_key_serialized
    <:
    (Libcrux.Kem.Kyber.Types.t_PrivateKey v_PRIVATE_KEY_SIZE &
      Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE)),
  sampling_A_error
  <:
  ((Libcrux.Kem.Kyber.Types.t_PrivateKey v_PRIVATE_KEY_SIZE &
      Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)
