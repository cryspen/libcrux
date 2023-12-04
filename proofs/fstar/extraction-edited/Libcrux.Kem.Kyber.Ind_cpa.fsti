module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val serialize_secret_key (#p:Spec.Kyber.params)
      (v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : Pure (t_Array u8 v_SERIALIZED_KEY_LEN)
      (requires (length private_key == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                 length public_key == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                 length implicit_rejection_value == Spec.Kyber.v_SHARED_SECRET_SIZE /\
                 v_SERIALIZED_KEY_LEN == Spec.Kyber.v_SECRET_KEY_SIZE p))
      (ensures (fun res -> res == Spec.Kyber.ind_cpa_serialize_secret_key p (private_key,public_key) implicit_rejection_value))
                 
val decrypt (#p:Spec.Kyber.params)
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (secret_key: t_Slice u8)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : Pure (t_Array u8 (sz 32))
      (requires (length secret_key == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                 v_CIPHERTEXT_SIZE == Spec.Kyber.v_CPA_PKE_CIPHERTEXT_SIZE p /\
                 v_VECTOR_U_ENCODED_SIZE == Spec.Kyber.v_C1_SIZE p /\
                 v_U_COMPRESSION_FACTOR == p.v_VECTOR_U_COMPRESSION_FACTOR))
      (ensures (fun res ->
                res == Spec.Kyber.ind_cpa_decrypt p secret_key ciphertext.f_value))


val encrypt (#p:Spec.Kyber.params)
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8{length randomness <. sz 33})
    : Pure (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE &
           Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)
      (requires (length public_key == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                 length randomness == Spec.Kyber.v_SHARED_SECRET_SIZE /\
                 v_CIPHERTEXT_SIZE == Spec.Kyber.v_CPA_PKE_CIPHERTEXT_SIZE p /\
                 v_T_AS_NTT_ENCODED_SIZE == Spec.Kyber.v_T_AS_NTT_ENCODED_SIZE p /\
                 v_C1_LEN == Spec.Kyber.v_C1_SIZE p))
      (ensures (fun (ct,err) ->
               let spec_result = Spec.Kyber.ind_cpa_encrypt p public_key message randomness in
               match err with
               | Core.Option.Option_None -> spec_result == Spec.Kyber.Ok (ct.f_value)
               | Core.Option.Option_Some _ -> spec_result == Spec.Kyber.Err Spec.Kyber.Error_RejectionSampling))
               

val generate_keypair (#p:Spec.Kyber.params)
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (key_generation_seed: t_Slice u8)
    : Pure ((Libcrux.Kem.Kyber.Types.t_PrivateKey v_PRIVATE_KEY_SIZE &
           Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
           Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)
      (requires (v_K == p.v_RANK /\
                 v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                 v_PRIVATE_KEY_SIZE == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                 length key_generation_seed == Spec.Kyber.v_CPA_PKE_KEY_GENERATION_SEED_SIZE))
      (ensures (fun ((sk,pk),err) ->
               let spec_result = Spec.Kyber.ind_cpa_generate_keypair p key_generation_seed in
               match err with
               | Core.Option.Option_None -> spec_result == Spec.Kyber.Ok (sk.f_value,pk.f_value)
               | Core.Option.Option_Some _ -> spec_result == Spec.Kyber.Err Spec.Kyber.Error_RejectionSampling))
