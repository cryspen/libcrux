module Libcrux.Kem.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val decapsulate (#p:Spec.Kyber.params)
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (secret_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : Pure (t_Array u8 (sz 32))
    (requires ( p == (let open Spec.Kyber in {v_RANK = v_K; v_ETA1; v_ETA2; v_VECTOR_U_COMPRESSION_FACTOR; v_VECTOR_V_COMPRESSION_FACTOR}) /\
                Spec.Kyber.valid_params p /\
                v_IMPLICIT_REJECTION_HASH_INPUT_SIZE == Spec.Kyber.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE p /\
                v_SECRET_KEY_SIZE == Spec.Kyber.v_SECRET_KEY_SIZE p /\
                v_CPA_SECRET_KEY_SIZE == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                v_CIPHERTEXT_SIZE == Spec.Kyber.v_CPA_PKE_CIPHERTEXT_SIZE p /\
                v_C1_SIZE == Spec.Kyber.v_C1_SIZE p /\
                v_T_AS_NTT_ENCODED_SIZE = Spec.Kyber.v_T_AS_NTT_ENCODED_SIZE p
               ))
    (ensures (fun res ->
                let open Spec.Kyber in
                let p = {v_RANK = v_K; v_ETA1; v_ETA2; v_VECTOR_U_COMPRESSION_FACTOR; v_VECTOR_V_COMPRESSION_FACTOR} in
                res == Spec.Kyber.ind_cca_decapsulate p secret_key.f_value ciphertext.f_value))

val encapsulate (#p:Spec.Kyber.params)
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
    : Pure (Core.Result.t_Result
           (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
            Libcrux.Kem.Kyber.Types.t_Error)
      (requires (
                p == (let open Spec.Kyber in {v_RANK = v_K; v_ETA1; v_ETA2; v_VECTOR_U_COMPRESSION_FACTOR; v_VECTOR_V_COMPRESSION_FACTOR}) /\
                Spec.Kyber.valid_params p /\
                v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                v_CIPHERTEXT_SIZE == Spec.Kyber.v_CPA_PKE_CIPHERTEXT_SIZE p /\
                v_C1_SIZE == Spec.Kyber.v_C1_SIZE p /\
                v_T_AS_NTT_ENCODED_SIZE = Spec.Kyber.v_T_AS_NTT_ENCODED_SIZE p
                ))

      (ensures (fun res ->
                let open Spec.Kyber in
                let p = {v_RANK = v_K; v_ETA1; v_ETA2; v_VECTOR_U_COMPRESSION_FACTOR; v_VECTOR_V_COMPRESSION_FACTOR} in
                let spec_result = Spec.Kyber.ind_cca_encapsulate p public_key.f_value randomness in
                match res with 
                | Core.Result.Result_Ok (cip,ss) -> spec_result == Ok(cip.f_value,ss)
                | Core.Result.Result_Err e -> spec_result = Err Error_RejectionSampling))

val generate_keypair (#p:Spec.Kyber.params)
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
    : Pure (Core.Result.t_Result
           (Libcrux.Kem.Kyber.Types.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
           Libcrux.Kem.Kyber.Types.t_Error)
      (requires (v_K == p.v_RANK /\ v_ETA1 == p.v_ETA1 /\
                v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                v_CPA_PRIVATE_KEY_SIZE == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                v_PRIVATE_KEY_SIZE == Spec.Kyber.v_SECRET_KEY_SIZE p
                ))

      (ensures (fun res -> 
                let spec_result = Spec.Kyber.ind_cca_generate_keypair p randomness in
                match res with 
                | Core.Result.Result_Ok (kp) -> spec_result == Spec.Kyber.Ok(kp.Libcrux.Kem.Kyber.Types.f_sk.f_value,kp.Libcrux.Kem.Kyber.Types.f_pk.f_value)
                | Core.Result.Result_Err e -> spec_result = Spec.Kyber.Err Spec.Kyber.Error_RejectionSampling))
