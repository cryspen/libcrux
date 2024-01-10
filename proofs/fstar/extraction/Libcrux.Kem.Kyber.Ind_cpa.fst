module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let into_padded_array (v_LEN: usize) (slice: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((Core.Slice.impl__len slice <: usize) <=. v_LEN <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: slice.len() <= LEN"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let out:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
  let out:t_Array u8 v_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = Core.Slice.impl__len slice <: usize }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice (out.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = Core.Slice.impl__len slice <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          slice
        <:
        t_Slice u8)
  in
  out

let sample_ring_element_cbd
      (v_K v_ETA2_RANDOMNESS_SIZE v_ETA2: usize)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
     =
  let error_1_:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let domain_separator, error_1_, prf_input:(u8 &
    t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K &
    t_Array u8 (sz 33)) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (domain_separator, error_1_, prf_input
        <:
        (u8 & t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K & t_Array u8 (sz 33))
      )
      (fun temp_0_ i ->
          let domain_separator, error_1_, prf_input:(u8 &
            t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K &
            t_Array u8 (sz 33)) =
            temp_0_
          in
          let i:usize = i in
          let prf_input:t_Array u8 (sz 33) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_input
              (sz 32)
              domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: t_Array u8 v_ETA2_RANDOMNESS_SIZE):t_Array u8 v_ETA2_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF v_ETA2_RANDOMNESS_SIZE
              (Rust_primitives.unsize prf_input <: t_Slice u8)
          in
          let error_1_:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize error_1_
              i
              (Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution v_ETA2
                  (Rust_primitives.unsize prf_output <: t_Slice u8)
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          domain_separator, error_1_, prf_input
          <:
          (u8 & t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K &
            t_Array u8 (sz 33)))
  in
  let hax_temp_output:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K = error_1_ in
  prf_input, domain_separator, hax_temp_output
  <:
  (t_Array u8 (sz 33) & u8 & t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)

let sample_vector_cbd_then_ntt
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
     =
  let re_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let domain_separator, prf_input, re_as_ntt:(u8 & t_Array u8 (sz 33) &
    t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (domain_separator, prf_input, re_as_ntt
        <:
        (u8 & t_Array u8 (sz 33) & t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      )
      (fun temp_0_ i ->
          let domain_separator, prf_input, re_as_ntt:(u8 & t_Array u8 (sz 33) &
            t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) =
            temp_0_
          in
          let i:usize = i in
          let prf_input:t_Array u8 (sz 33) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_input
              (sz 32)
              domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: t_Array u8 v_ETA_RANDOMNESS_SIZE):t_Array u8 v_ETA_RANDOMNESS_SIZE =
            Libcrux.Kem.Kyber.Hash_functions.v_PRF v_ETA_RANDOMNESS_SIZE
              (Rust_primitives.unsize prf_input <: t_Slice u8)
          in
          let r:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution v_ETA
              (Rust_primitives.unsize prf_output <: t_Slice u8)
          in
          let re_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_binomially_sampled_ring_element r
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          domain_separator, prf_input, re_as_ntt
          <:
          (u8 & t_Array u8 (sz 33) &
            t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K))
  in
  re_as_ntt, domain_separator
  <:
  (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K & u8)

let compress_then_serialize_u
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (input: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
     =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let out:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Iter.Traits.Collect.f_into_iter input
                <:
                Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K))
      out
      (fun out temp_1_ ->
          let out:t_Array u8 v_OUT_LEN = out in
          let i, re:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
            ({
                Core.Ops.Range.f_start = i *! (v_OUT_LEN /! v_K <: usize) <: usize;
                Core.Ops.Range.f_end = (i +! sz 1 <: usize) *! (v_OUT_LEN /! v_K <: usize) <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
            (Core.Slice.impl__copy_from_slice (out.[ {
                      Core.Ops.Range.f_start = i *! (v_OUT_LEN /! v_K <: usize) <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! sz 1 <: usize) *! (v_OUT_LEN /! v_K <: usize) <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
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
              <:
              t_Slice u8)
          <:
          t_Array u8 v_OUT_LEN)
  in
  out

let deserialize_then_decompress_u
      (v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR: usize)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
     =
  let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize ciphertext <: t_Slice u8)
                  ((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
                      v_U_COMPRESSION_FACTOR
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
      (fun u_as_ntt temp_1_ ->
          let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
            u_as_ntt
          in
          let i, u_bytes:(usize & t_Slice u8) = temp_1_ in
          let u:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            Libcrux.Kem.Kyber.Serialize.deserialize_then_decompress_ring_element_u v_U_COMPRESSION_FACTOR
              u_bytes
          in
          let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize u_as_ntt
              i
              (Libcrux.Kem.Kyber.Ntt.ntt_vector_u v_U_COMPRESSION_FACTOR u
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          u_as_ntt)
  in
  u_as_ntt

let deserialize_public_key (v_K: usize) (public_key: t_Slice u8) =
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact public_key
                  Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      tt_as_ntt
      (fun tt_as_ntt temp_1_ ->
          let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
            tt_as_ntt
          in
          let i, tt_as_ntt_bytes:(usize & t_Slice u8) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
            i
            (Libcrux.Kem.Kyber.Serialize.deserialize_to_uncompressed_ring_element tt_as_ntt_bytes
              <:
              Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          <:
          t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
  in
  tt_as_ntt

let deserialize_secret_key (v_K: usize) (secret_key: t_Slice u8) =
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
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
      (fun secret_as_ntt temp_1_ ->
          let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
            secret_as_ntt
          in
          let i, secret_bytes:(usize & t_Slice u8) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize secret_as_ntt
            i
            (Libcrux.Kem.Kyber.Serialize.deserialize_to_uncompressed_ring_element secret_bytes
              <:
              Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          <:
          t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
  in
  secret_as_ntt

let decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
     =
  let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    deserialize_then_decompress_u v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR ciphertext
  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Serialize.deserialize_then_decompress_ring_element_v v_V_COMPRESSION_FACTOR
      (ciphertext.[ { Core.Ops.Range.f_start = v_VECTOR_U_ENCODED_SIZE }
          <:
          Core.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    deserialize_secret_key v_K secret_key
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
     =
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    deserialize_public_key v_K public_key
  in
  let seed:t_Slice u8 =
    public_key.[ { Core.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE }
      <:
      Core.Ops.Range.t_RangeFrom usize ]
  in
  let v_A_transpose:t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K =
    Libcrux.Kem.Kyber.Matrix.sample_matrix_A v_K
      (into_padded_array (sz 34) seed <: t_Array u8 (sz 34))
      false
  in
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) = into_padded_array (sz 33) randomness in
  let r_as_ntt, domain_separator:(t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K &
    u8) =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE prf_input 0uy
  in
  let tmp0, tmp1, out:(t_Array u8 (sz 33) & u8 &
    t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) =
    sample_ring_element_cbd v_K v_ETA2_RANDOMNESS_SIZE v_ETA2 prf_input domain_separator
  in
  let prf_input:t_Array u8 (sz 33) = tmp0 in
  let domain_separator:u8 = tmp1 in
  let error_1_:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K = out in
  let prf_input:t_Array u8 (sz 33) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_input (sz 32) domain_separator
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
    compress_then_serialize_u v_K v_C1_LEN v_U_COMPRESSION_FACTOR v_BLOCK_LEN u
  in
  let c2:t_Array u8 v_C2_LEN =
    Libcrux.Kem.Kyber.Serialize.compress_then_serialize_ring_element_v v_V_COMPRESSION_FACTOR
      v_C2_LEN
      v
  in
  let (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE):t_Array u8 v_CIPHERTEXT_SIZE =
    into_padded_array v_CIPHERTEXT_SIZE (Rust_primitives.unsize c1 <: t_Slice u8)
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from ciphertext
      ({ Core.Ops.Range.f_start = v_C1_LEN } <: Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice (ciphertext.[ { Core.Ops.Range.f_start = v_C1_LEN }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (Core.Array.impl_23__as_slice v_C2_LEN c2 <: t_Slice u8)
        <:
        t_Slice u8)
  in
  ciphertext

let serialize_secret_key
      (v_K v_OUT_LEN: usize)
      (key: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
     =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let out:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Iter.Traits.Collect.f_into_iter key
                <:
                Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K))
      out
      (fun out temp_1_ ->
          let out:t_Array u8 v_OUT_LEN = out in
          let i, re:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
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
            (Core.Slice.impl__copy_from_slice (out.[ {
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
                    Core.Ops.Range.t_Range usize ]
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

let serialize_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (tt_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (seed_for_a: t_Slice u8)
     =
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.repeat 0uy v_PUBLIC_KEY_SIZE
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range public_key_serialized
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_RANKED_BYTES_PER_RING_ELEMENT }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice (public_key_serialized.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = v_RANKED_BYTES_PER_RING_ELEMENT
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (Rust_primitives.unsize (serialize_secret_key v_K
                  v_RANKED_BYTES_PER_RING_ELEMENT
                  tt_as_ntt
                <:
                t_Array u8 v_RANKED_BYTES_PER_RING_ELEMENT)
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from public_key_serialized
      ({ Core.Ops.Range.f_start = v_RANKED_BYTES_PER_RING_ELEMENT }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice (public_key_serialized.[ {
                Core.Ops.Range.f_start = v_RANKED_BYTES_PER_RING_ELEMENT
              }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          seed_for_a
        <:
        t_Slice u8)
  in
  public_key_serialized

let generate_keypair
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (key_generation_seed: t_Slice u8)
     =
  let hashed:t_Array u8 (sz 64) = Libcrux.Kem.Kyber.Hash_functions.v_G key_generation_seed in
  let seed_for_A, seed_for_secret_and_error:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8) (sz 32)
  in
  let v_A_transpose:t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K =
    Libcrux.Kem.Kyber.Matrix.sample_matrix_A v_K
      (into_padded_array (sz 34) seed_for_A <: t_Array u8 (sz 34))
      true
  in
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) =
    into_padded_array (sz 33) seed_for_secret_and_error
  in
  let secret_as_ntt, domain_separator:(t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      v_K &
    u8) =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE prf_input 0uy
  in
  let error_as_ntt, _:(t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K & u8) =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE prf_input domain_separator
  in
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Matrix.compute_As_plus_e v_K v_A_transpose secret_as_ntt error_as_ntt
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    serialize_public_key v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE tt_as_ntt seed_for_A
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    serialize_secret_key v_K v_PRIVATE_KEY_SIZE secret_as_ntt
  in
  secret_key_serialized, public_key_serialized
  <:
  (t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE)
