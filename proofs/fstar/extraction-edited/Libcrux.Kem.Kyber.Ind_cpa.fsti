module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val into_padded_array (v_LEN: usize) (slice: t_Slice u8) :
    Pure (t_Array u8 v_LEN)
    (requires (length slice <=. v_LEN))
    (ensures (fun res ->  Seq.slice res 0 (Seq.length slice) == slice))

val sample_vector_cbd (#p:Spec.Kyber.params)
      (v_K v_ETA2_RANDOMNESS_SIZE v_ETA2: usize)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : Pure (t_Array u8 (sz 33) & u8 & t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
      (requires v domain_separator <= v v_K /\ v_K <=. sz 4 /\
                v_K = p.v_RANK /\ v_ETA2 = p.v_ETA2 /\
                v_ETA2_RANDOMNESS_SIZE = Spec.Kyber.v_ETA2_RANDOMNESS_SIZE p)
      (ensures (fun (prf,ds,x) -> v ds == v domain_separator + v v_K /\
                Seq.slice prf 0 32 == Seq.slice prf_input 0 32 /\
                Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p x ==
                Spec.Kyber.sample_vector_cbd #p (Seq.slice prf_input 0 32) (sz (v domain_separator))))


val sample_vector_cbd_then_ntt (#p:Spec.Kyber.params)
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8{v domain_separator <= v v_K /\ v_K <=. sz 4})
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K & u8) 
      (requires (v_K == p.v_RANK /\ v_ETA == p.v_ETA1 /\ v_ETA_RANDOMNESS_SIZE == Spec.Kyber.v_ETA1_RANDOMNESS_SIZE p))
      (ensures (fun (x,ds) -> v ds == v domain_separator + v v_K /\
                Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p x ==
                Spec.Kyber.sample_vector_cbd_then_ntt #p (Seq.slice prf_input 0 32) (sz (v domain_separator))))

val compress_then_serialize_u (#p:Spec.Kyber.params)
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (input: t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
    : Pure (t_Array u8 v_OUT_LEN)
      (requires (v_K == p.v_RANK /\ v_OUT_LEN == Spec.Kyber.v_C1_SIZE p /\
                 v_COMPRESSION_FACTOR == p.v_VECTOR_U_COMPRESSION_FACTOR /\
                 v_BLOCK_LEN = Spec.Kyber.v_C1_BLOCK_SIZE p))
      (ensures (fun res -> 
        res == Spec.Kyber.compress_then_encode_u p 
               (Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p input)))

val deserialize_then_decompress_u (#p:Spec.Kyber.params)
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR: usize)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) 
      (requires v_K == p.v_RANK /\
                v_CIPHERTEXT_SIZE == Spec.Kyber.v_CPA_PKE_CIPHERTEXT_SIZE p /\
                v_VECTOR_U_ENCODED_SIZE == Spec.Kyber.v_C1_SIZE p /\
                v_U_COMPRESSION_FACTOR == p.v_VECTOR_U_COMPRESSION_FACTOR)
      (ensures fun res ->
        Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p res ==
        Spec.Kyber.(vector_ntt (decode_then_decompress_u p (Seq.slice ciphertext 0 (v (Spec.Kyber.v_C1_SIZE p))))))

val deserialize_public_key (#p:Spec.Kyber.params) 
    (v_K: usize) (public_key: t_Array u8 (Spec.Kyber.v_T_AS_NTT_ENCODED_SIZE p))
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
      (requires v_K == p.v_RANK /\
                length public_key == Spec.Kyber.v_RANKED_BYTES_PER_RING_ELEMENT p)
      (ensures fun res -> 
        Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b res ==
        Spec.Kyber.vector_decode_12 #p public_key)
   
val deserialize_secret_key (#p:Spec.Kyber.params) (v_K: usize) (secret_key: t_Slice u8)
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
      (requires v_K == p.v_RANK /\
                length secret_key == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p)
      (ensures fun res ->
         Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p res ==
         Spec.Kyber.vector_decode_12 #p secret_key)
    

val decrypt (#p:Spec.Kyber.params)
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Pure (t_Array u8 (sz 32))
      (requires (v_K == p.v_RANK /\
                 length secret_key == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                 v_CIPHERTEXT_SIZE == Spec.Kyber.v_CPA_PKE_CIPHERTEXT_SIZE p /\
                 v_VECTOR_U_ENCODED_SIZE == Spec.Kyber.v_C1_SIZE p /\
                 v_U_COMPRESSION_FACTOR == p.v_VECTOR_U_COMPRESSION_FACTOR /\
                 v_V_COMPRESSION_FACTOR == p.v_VECTOR_V_COMPRESSION_FACTOR))
      (ensures (fun res ->
                res == Spec.Kyber.ind_cpa_decrypt p secret_key ciphertext))


val encrypt (#p:Spec.Kyber.params)
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8{length randomness <. sz 33})
    : Pure (t_Array u8 v_CIPHERTEXT_SIZE)
      (requires (v_K == p.v_RANK /\
                 v_ETA1 = p.v_ETA1 /\
                 v_ETA1_RANDOMNESS_SIZE = Spec.Kyber.v_ETA1_RANDOMNESS_SIZE p /\
                 v_ETA2 = p.v_ETA2 /\
                 v_BLOCK_LEN == Spec.Kyber.v_C1_BLOCK_SIZE p /\
                 v_ETA2_RANDOMNESS_SIZE = Spec.Kyber.v_ETA2_RANDOMNESS_SIZE p /\
                 v_U_COMPRESSION_FACTOR == p.v_VECTOR_U_COMPRESSION_FACTOR /\
                 v_V_COMPRESSION_FACTOR == p.v_VECTOR_V_COMPRESSION_FACTOR /\
                 length public_key == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                 length randomness == Spec.Kyber.v_SHARED_SECRET_SIZE /\
                 v_CIPHERTEXT_SIZE == Spec.Kyber.v_CPA_PKE_CIPHERTEXT_SIZE p /\
                 v_T_AS_NTT_ENCODED_SIZE == Spec.Kyber.v_T_AS_NTT_ENCODED_SIZE p /\
                 v_C1_LEN == Spec.Kyber.v_C1_SIZE p /\
                 v_C2_LEN == Spec.Kyber.v_C2_SIZE p))
      (ensures (fun ct -> ct == Spec.Kyber.ind_cpa_encrypt p public_key message randomness))
               
val serialize_secret_key (#p:Spec.Kyber.params)
      (v_K v_OUT_LEN: usize)
      (key: t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
    : Pure (t_Array u8 v_OUT_LEN)
      (requires (v_K == p.v_RANK /\ v_OUT_LEN == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p))
      (ensures (fun res -> 
        res == Spec.Kyber.vector_encode_12 #p 
          (Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p key)))
      
val serialize_public_key (#p:Spec.Kyber.params)
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (tt_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
      (seed_for_a: t_Slice u8)
      : Pure (t_Array u8 v_PUBLIC_KEY_SIZE)
        (requires (v_K == p.v_RANK /\
                   v_RANKED_BYTES_PER_RING_ELEMENT == Spec.Kyber.v_RANKED_BYTES_PER_RING_ELEMENT p /\
                   v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                   length seed_for_a == sz 32))
        (ensures (fun res -> res == Seq.append (Spec.Kyber.vector_encode_12 
                              (Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p tt_as_ntt))
                            seed_for_a))

val generate_keypair (#p:Spec.Kyber.params)
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (key_generation_seed: t_Slice u8)
    : Pure (t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE)
      (requires (v_K == p.v_RANK /\
                 v_ETA1 == p.v_ETA1 /\
                 v_ETA1_RANDOMNESS_SIZE == Spec.Kyber.v_ETA1_RANDOMNESS_SIZE p /\
                 v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                 v_PRIVATE_KEY_SIZE == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                 v_RANKED_BYTES_PER_RING_ELEMENT == Spec.Kyber.v_RANKED_BYTES_PER_RING_ELEMENT p /\
                 length key_generation_seed == Spec.Kyber.v_CPA_PKE_KEY_GENERATION_SEED_SIZE))
      (ensures (fun (sk,pk) -> (sk,pk) == Spec.Kyber.ind_cpa_generate_keypair p key_generation_seed))
 
    
