module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val into_padded_array (v_LEN: usize) (slice: t_Slice u8) :
    Pure (t_Array u8 v_LEN)
    (requires (length slice <=. v_LEN))
    (ensures (fun res -> Seq.slice res 0 (Seq.length slice) == slice))

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
 
    
