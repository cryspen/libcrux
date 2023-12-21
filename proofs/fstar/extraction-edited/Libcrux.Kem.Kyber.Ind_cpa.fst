module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 50"
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

unfold let acc_t v_K = (u8 & t_Array u8 (sz 33) & t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
unfold let inv_t v_K = acc_t v_K -> usize -> Type

val sample_vector_cbd (#p:Spec.Kyber.params)
      (v_K v_ETA2_RANDOMNESS_SIZE v_ETA2: usize)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : Pure (t_Array u8 (sz 33) & u8 & t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (requires v domain_separator <= v v_K /\ v_K <=. sz 4 /\
                v_K = p.v_RANK /\ v_ETA2 = p.v_ETA2 /\
                v_ETA2_RANDOMNESS_SIZE = Spec.Kyber.v_ETA2_RANDOMNESS_SIZE p)
      (ensures (fun (prf,ds,x) -> v ds == v domain_separator + v v_K /\
                Seq.slice prf 0 32 == Seq.slice prf_input 0 32 /\
                Libcrux.Kem.Kyber.Arithmetic.to_spec_vector #p x ==
                Spec.Kyber.sample_vector_cbd #p (Seq.slice prf_input 0 32) (sz (v domain_separator))))


let sample_vector_cbd (#p:Spec.Kyber.params)
      (v_K v_ETA2_RANDOMNESS_SIZE v_ETA2: usize)
      (prf_input: t_Array u8 (sz 33)) domain_separator = 
  let error_1_:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let orig_domain_separator = domain_separator in
  [@ inline_let]
  let inv : inv_t v_K = fun (acc:acc_t v_K) (i:usize) ->
    let (domain_separator,prf_input,error_1_) = acc in
    if (i >=. sz 0 && i <=. v_K)
    then 
      domain_separator = orig_domain_separator +! (mk_int #u8_inttype (v i))
    else true in
  let (domain_separator, prf_input, error_1_):acc_t v_K = 
    Rust_primitives.Iterators.foldi_range #_ #(acc_t v_K)  #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
      (domain_separator, prf_input, error_1_)
      (fun temp_0_ i ->
          let domain_separator, prf_input, error_1_:acc_t v_K =
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
              (Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution #p v_ETA2
                  (Rust_primitives.unsize prf_output <: t_Slice u8)
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          domain_separator, prf_input, error_1_)
  in
  let hax_temp_output:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K = error_1_ in
  admit(); //P-F
  prf_input, domain_separator, hax_temp_output
  <:
  (t_Array u8 (sz 33) & u8 & t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)

val sample_vector_cbd_then_ntt (#p:Spec.Kyber.params)
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8{v domain_separator <= v v_K /\ v_K <=. sz 4})
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K & u8) 
      (requires (v_K == p.v_RANK /\ v_ETA == p.v_ETA1 /\ v_ETA_RANDOMNESS_SIZE == Spec.Kyber.v_ETA1_RANDOMNESS_SIZE p))
      (ensures (fun (x,ds) -> v ds == v domain_separator + v v_K /\
                Libcrux.Kem.Kyber.Arithmetic.to_spec_vector #p x ==
                Spec.Kyber.sample_vector_cbd_then_ntt #p (Seq.slice prf_input 0 32) (sz (v domain_separator))))

let sample_vector_cbd_then_ntt (#p:Spec.Kyber.params)
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (prf_input: t_Array u8 (sz 33)) domain_separator =
  let re_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let orig_domain_separator = domain_separator in
  [@ inline_let]
  let inv : inv_t v_K = fun (acc:acc_t v_K) (i:usize) ->
    let (domain_separator,prf_input,re_as_ntt) = acc in
    if (i >=. sz 0 && i <=. v_K)
    then 
      domain_separator = orig_domain_separator +! (mk_int #u8_inttype (v i))
    else true in
  let (domain_separator, prf_input, re_as_ntt):acc_t v_K = 
    Rust_primitives.Iterators.foldi_range #_ #(acc_t v_K)  #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
      (domain_separator, prf_input, re_as_ntt)
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
            Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution #p v_ETA
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
  admit(); //P-F
  re_as_ntt, domain_separator
  <:
  (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K & u8)

val compress_then_serialize_u (#p:Spec.Kyber.params)
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (input: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Pure (t_Array u8 v_OUT_LEN)
      (requires (v_K == p.v_RANK /\ v_OUT_LEN == Spec.Kyber.v_C1_SIZE p /\
                 v_COMPRESSION_FACTOR == p.v_VECTOR_U_COMPRESSION_FACTOR /\
                 v_BLOCK_LEN = Spec.Kyber.v_C1_BLOCK_SIZE p))
      (ensures (fun res -> 
        res == Spec.Kyber.compress_then_encode_u p 
               (Libcrux.Kem.Kyber.Arithmetic.to_spec_vector #p input)))

let compress_then_serialize_u (#p:Spec.Kyber.params)
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (input: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let orig_out = out in
  let acc_t = t_Array u8 v_OUT_LEN in
  [@ inline_let]
  let inv = fun (acc:acc_t) (i:usize) -> True in
  let out:t_Array u8 v_OUT_LEN =
    Rust_primitives.Iterators.foldi_slice #Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement  #acc_t #inv
      input
      out
      (fun out temp_1_ ->
          let out:t_Array u8 v_OUT_LEN = out in
          let i, re:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) = temp_1_ in
          assert (i <. v_K);
          assert (v i + 1  <=  v v_K);
          assert (((v i + 1) * (v v_OUT_LEN / v v_K)) <= v v_OUT_LEN);
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
                (Rust_primitives.unsize (Libcrux.Kem.Kyber.Serialize.compress_then_serialize_ring_element_u #p
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
  admit();//P-F
  out

#push-options "--split_queries always"
val deserialize_then_decompress_u (#p:Spec.Kyber.params)
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR: usize)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) 
      (requires v_K == p.v_RANK /\
                v_CIPHERTEXT_SIZE == Spec.Kyber.v_CPA_PKE_CIPHERTEXT_SIZE p /\
                v_VECTOR_U_ENCODED_SIZE == Spec.Kyber.v_C1_SIZE p /\
                v_U_COMPRESSION_FACTOR == p.v_VECTOR_U_COMPRESSION_FACTOR)
      (ensures fun res ->
        Libcrux.Kem.Kyber.Arithmetic.to_spec_vector #p res ==
        Spec.Kyber.(vector_ntt (decode_then_decompress_u p (Seq.slice ciphertext 0 (v (Spec.Kyber.v_C1_SIZE p))))))

let deserialize_then_decompress_u (#p:Spec.Kyber.params)
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR: usize)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE) =
  let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let acc_t1 = t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K in
  [@ inline_let]
  let inv = fun (acc:acc_t1) (i:usize) -> True in
  let sl : t_Slice u8 = ciphertext.[ 
                      { Core.Ops.Range.f_end = v_VECTOR_U_ENCODED_SIZE  } <: Core.Ops.Range.t_RangeTo usize ] in
  assert (length sl == v_VECTOR_U_ENCODED_SIZE);
  let chunk_len = ((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
                      v_U_COMPRESSION_FACTOR
                      <:
                      usize) /!
                    sz 8
                    <:
                    usize) in
  FStar.Math.Lemmas.cancel_mul_mod (v p.v_RANK) (v (Spec.Kyber.v_C1_BLOCK_SIZE p)) ;
  assert (Seq.length sl % v (Spec.Kyber.v_C1_BLOCK_SIZE p) = 0);
  assert (Seq.length sl == v (Spec.Kyber.v_C1_SIZE p));
  assert (Seq.length sl / v (Spec.Kyber.v_C1_BLOCK_SIZE p) == v v_K);
  let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
   Rust_primitives.Iterators.foldi_chunks_exact #u8 #acc_t1 #inv
      sl
      chunk_len
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
  admit(); //P-F
  u_as_ntt

val deserialize_public_key (#p:Spec.Kyber.params) 
    (v_K v_T_AS_NTT_ENCODED_SIZE: usize) (public_key: t_Slice u8)
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (requires v_K == p.v_RANK /\
                length public_key == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                v_T_AS_NTT_ENCODED_SIZE == Spec.Kyber.v_T_AS_NTT_ENCODED_SIZE p)
      (ensures fun res -> 
        Libcrux.Kem.Kyber.Arithmetic.to_spec_vector res ==
        Spec.Kyber.vector_decode_12 #p (slice public_key (sz 0) v_T_AS_NTT_ENCODED_SIZE))
   
let deserialize_public_key (#p:Spec.Kyber.params) 
    (v_K v_T_AS_NTT_ENCODED_SIZE: usize) (public_key: t_Slice u8) =
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let acc_t = t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K in
  [@ inline_let]
  let inv = fun (acc:acc_t) (i:usize) -> True in
  let sl : t_Slice u8 = public_key.[ 
                      { Core.Ops.Range.f_end = v_T_AS_NTT_ENCODED_SIZE } <: Core.Ops.Range.t_RangeTo usize ] in
  let chunk_len = Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT in
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
   Rust_primitives.Iterators.foldi_chunks_exact #u8 #acc_t #inv
      sl
      chunk_len
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
  admit(); //P-F
  tt_as_ntt 

val deserialize_secret_key (#p:Spec.Kyber.params) (v_K: usize) (secret_key: t_Slice u8)
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (requires v_K == p.v_RANK /\
                length secret_key == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p)
      (ensures fun res ->
         Libcrux.Kem.Kyber.Arithmetic.to_spec_vector #p res ==
         Spec.Kyber.vector_decode_12 #p secret_key)
    
let deserialize_secret_key (#p:Spec.Kyber.params) (v_K: usize) (secret_key: t_Slice u8) =
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let acc_t = t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K in
  [@ inline_let]
  let inv = fun (acc:acc_t) (i:usize) -> True in
  let sl : t_Slice u8 = secret_key in
  let chunk_len = Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT in
  assert(v chunk_len == 384);
  assert(Seq.length secret_key == v (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p));
  assert(Seq.length secret_key == (v v_K * 256 * 12)/8);
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
   Rust_primitives.Iterators.foldi_chunks_exact #u8 #acc_t #inv
      sl
      chunk_len
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
  admit(); //P-F
  secret_as_ntt
#pop-options

let decrypt #p
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE) = 
  let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    deserialize_then_decompress_u #p v_K
      v_CIPHERTEXT_SIZE
      v_VECTOR_U_ENCODED_SIZE
      v_U_COMPRESSION_FACTOR
      ciphertext
  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Serialize.deserialize_then_decompress_ring_element_v #p v_V_COMPRESSION_FACTOR
      (ciphertext.[ { Core.Ops.Range.f_start = v_VECTOR_U_ENCODED_SIZE }
          <:
          Core.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    deserialize_secret_key #p v_K secret_key
  in
  let message:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Matrix.compute_message #p v_K v secret_as_ntt u_as_ntt
  in
  let res = Libcrux.Kem.Kyber.Serialize.compress_then_serialize_message message in
  res
  
#push-options "--z3rlimit 200"
let encrypt #p
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8) =
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    deserialize_public_key #p v_K v_T_AS_NTT_ENCODED_SIZE public_key
  in
  let seed:t_Slice u8 =
    public_key.[ { Core.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE }
      <:
      Core.Ops.Range.t_RangeFrom usize ]
  in
  let v_A_transpose:t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K =
    Libcrux.Kem.Kyber.Matrix.sample_matrix_A #p v_K
      (into_padded_array (sz 34) seed <: t_Array u8 (sz 34))
      false
  in
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) = into_padded_array (sz 33) randomness in
  let r_as_ntt, domain_separator:(t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K &
    u8) =
    sample_vector_cbd_then_ntt #p v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE prf_input 0uy
  in
  assert (v domain_separator == v v_K);
  let tmp0, tmp1, out:(t_Array u8 (sz 33) & u8 &
    t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) =
    sample_vector_cbd #p v_K v_ETA2_RANDOMNESS_SIZE v_ETA2 prf_input domain_separator
  in
  let prf_input:t_Array u8 (sz 33) = tmp0 in
  let domain_separator:u8 = tmp1 in
  let error_1_:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K = out in
  let prf_input:t_Array u8 (sz 33) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_input (sz 32) domain_separator
  in
  assert (Seq.equal prf_input (Seq.append randomness (Seq.create 1 domain_separator)));
  assert (prf_input == Seq.append randomness (Seq.create 1 domain_separator));
  let (prf_output: t_Array u8 v_ETA2_RANDOMNESS_SIZE):t_Array u8 v_ETA2_RANDOMNESS_SIZE =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF v_ETA2_RANDOMNESS_SIZE
      (Rust_primitives.unsize prf_input <: t_Slice u8)
  in
  let error_2_:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution #p v_ETA2
      (Rust_primitives.unsize prf_output <: t_Slice u8)
  in
  let u:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Matrix.compute_vector_u #p v_K v_A_transpose r_as_ntt error_1_
  in
  let message_as_ring_element:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Serialize.deserialize_then_decompress_message message
  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Matrix.compute_ring_element_v #p v_K
      tt_as_ntt
      r_as_ntt
      error_2_
      message_as_ring_element
  in
  let c1:t_Array u8 v_C1_LEN =
    compress_then_serialize_u #p v_K v_C1_LEN v_U_COMPRESSION_FACTOR v_BLOCK_LEN u
  in
  let c2:t_Array u8 v_C2_LEN =
    Libcrux.Kem.Kyber.Serialize.compress_then_serialize_ring_element_v #p v_V_COMPRESSION_FACTOR
      v_C2_LEN
      v
  in
  assert (v_C1_LEN = Spec.Kyber.v_C1_SIZE p);
  assert (v_C2_LEN = Spec.Kyber.v_C2_SIZE p);
  assert (v_CIPHERTEXT_SIZE == v_C1_LEN +! v_C2_LEN);
  assert (v_C1_LEN <=. v_CIPHERTEXT_SIZE);
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
  lemma_slice_append ciphertext c1 c2;
  ciphertext
#pop-options

val serialize_secret_key (#p:Spec.Kyber.params)
      (v_K v_OUT_LEN: usize)
      (key: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Pure (t_Array u8 v_OUT_LEN)
      (requires (v_K == p.v_RANK /\ v_OUT_LEN == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p))
      (ensures (fun res -> 
        res == Spec.Kyber.vector_encode_12 #p 
          (Libcrux.Kem.Kyber.Arithmetic.to_spec_vector #p key)))
      
let serialize_secret_key (#p:Spec.Kyber.params)
      (v_K v_OUT_LEN: usize)
      (key: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let orig_out = out in
  let acc_t = t_Array u8 v_OUT_LEN in
  [@ inline_let]
  let inv = fun (acc:acc_t) (i:usize) -> True in
  let out:t_Array u8 v_OUT_LEN =
    Rust_primitives.Iterators.foldi_slice #Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement  #acc_t #inv
      key
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
  admit(); //P-F
  out

val serialize_public_key (#p:Spec.Kyber.params)
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (tt_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (seed_for_a: t_Slice u8)
      : Pure (t_Array u8 v_PUBLIC_KEY_SIZE)
        (requires (v_K == p.v_RANK /\
                   v_RANKED_BYTES_PER_RING_ELEMENT == Spec.Kyber.v_RANKED_BYTES_PER_RING_ELEMENT p /\
                   v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                   length seed_for_a == sz 32))
        (ensures (fun res -> res == Seq.append (Spec.Kyber.vector_encode_12 
                              (Libcrux.Kem.Kyber.Arithmetic.to_spec_vector #p tt_as_ntt))
                            seed_for_a))

let serialize_public_key (#p:Spec.Kyber.params)
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (tt_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (seed_for_a: t_Slice u8) =
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
          (Rust_primitives.unsize (serialize_secret_key #p v_K
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
  lemma_slice_append public_key_serialized
    (Spec.Kyber.vector_encode_12 (Libcrux.Kem.Kyber.Arithmetic.to_spec_vector #p tt_as_ntt))
    seed_for_a;
  public_key_serialized


let generate_keypair #p
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (key_generation_seed: t_Slice u8) =
  let hashed:t_Array u8 (sz 64) = Libcrux.Kem.Kyber.Hash_functions.v_G key_generation_seed in
  let seed_for_A, seed_for_secret_and_error:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8) (sz 32)
  in
  let v_A_transpose:t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K =
    Libcrux.Kem.Kyber.Matrix.sample_matrix_A #p v_K
      (into_padded_array (sz 34) seed_for_A <: t_Array u8 (sz 34))
      true
  in
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) =
    into_padded_array (sz 33) seed_for_secret_and_error
  in
  let secret_as_ntt, domain_separator:(t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      v_K &
    u8) =
    sample_vector_cbd_then_ntt #p v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE prf_input 0uy
  in
  let error_as_ntt, _:(t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K & u8) =
    sample_vector_cbd_then_ntt #p v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE prf_input domain_separator
  in
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Matrix.compute_As_plus_e #p v_K v_A_transpose secret_as_ntt error_as_ntt
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    serialize_public_key #p v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE tt_as_ntt seed_for_A
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    serialize_secret_key #p v_K v_PRIVATE_KEY_SIZE secret_as_ntt
  in
  let res = 
  secret_key_serialized, public_key_serialized
  <:
  (t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE)
  in
  res
