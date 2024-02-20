module Libcrux.Kem.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_MlKemSharedSecret = t_Array u8 (sz 32)

let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +!
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

val serialize_kem_secret_key (#p:Spec.Kyber.params)
      (v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : Pure (t_Array u8 v_SERIALIZED_KEY_LEN)
      (requires (length private_key == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                 length public_key == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                 length implicit_rejection_value == Spec.Kyber.v_SHARED_SECRET_SIZE /\
                 v_SERIALIZED_KEY_LEN == Spec.Kyber.v_SECRET_KEY_SIZE p))
      (ensures (fun res -> res ==
                Seq.append private_key (
                Seq.append public_key (
                Seq.append (Libcrux.Kem.Kyber.Hash_functions.v_H public_key) implicit_rejection_value))))

val decapsulate (#p:Spec.Kyber.params)
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (secret_key: Libcrux.Kem.Kyber.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    : Pure (t_Array u8 (sz 32))
    (requires ( p == (let open Spec.Kyber in {v_RANK = v_K; v_ETA1; v_ETA2; v_VECTOR_U_COMPRESSION_FACTOR; v_VECTOR_V_COMPRESSION_FACTOR}) /\
                Spec.Kyber.valid_params p /\
                v_ETA1_RANDOMNESS_SIZE == Spec.Kyber.v_ETA1_RANDOMNESS_SIZE p /\
                v_ETA2_RANDOMNESS_SIZE == Spec.Kyber.v_ETA2_RANDOMNESS_SIZE p /\
                v_IMPLICIT_REJECTION_HASH_INPUT_SIZE == Spec.Kyber.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE p /\
                v_SECRET_KEY_SIZE == Spec.Kyber.v_SECRET_KEY_SIZE p /\
                v_CPA_SECRET_KEY_SIZE == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                v_CIPHERTEXT_SIZE == Spec.Kyber.v_CPA_PKE_CIPHERTEXT_SIZE p /\
                v_C1_SIZE == Spec.Kyber.v_C1_SIZE p /\
                v_C1_BLOCK_SIZE == Spec.Kyber.v_C1_BLOCK_SIZE p /\
                v_C2_SIZE == Spec.Kyber.v_C2_SIZE p /\
                v_T_AS_NTT_ENCODED_SIZE = Spec.Kyber.v_T_AS_NTT_ENCODED_SIZE p
               ))
    (ensures (fun res ->
                res == Spec.Kyber.ind_cca_decapsulate p secret_key.f_value ciphertext.f_value))

val encapsulate (#p:Spec.Kyber.params)
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: Libcrux.Kem.Kyber.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
    : Pure (Libcrux.Kem.Kyber.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
     (requires (p == (let open Spec.Kyber in {v_RANK = v_K; v_ETA1; v_ETA2; v_VECTOR_U_COMPRESSION_FACTOR; v_VECTOR_V_COMPRESSION_FACTOR}) /\
                Spec.Kyber.valid_params p /\
                v_ETA1_RANDOMNESS_SIZE == Spec.Kyber.v_ETA1_RANDOMNESS_SIZE p /\
                v_ETA2_RANDOMNESS_SIZE == Spec.Kyber.v_ETA2_RANDOMNESS_SIZE p /\
                v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                v_CIPHERTEXT_SIZE == Spec.Kyber.v_CPA_PKE_CIPHERTEXT_SIZE p /\
                v_C1_SIZE == Spec.Kyber.v_C1_SIZE p /\
                v_C2_SIZE == Spec.Kyber.v_C2_SIZE p /\
                v_T_AS_NTT_ENCODED_SIZE = Spec.Kyber.v_T_AS_NTT_ENCODED_SIZE p /\
                v_VECTOR_U_BLOCK_LEN == Spec.Kyber.v_C1_BLOCK_SIZE p
                ))

      (ensures (fun (ct,ss) ->
                (ct.f_value,ss) == Spec.Kyber.ind_cca_encapsulate p public_key.f_value randomness))

val validate_public_key (#p:Spec.Kyber.params)
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
    : Prims.Pure bool
      (requires (v_K == p.v_RANK /\
                 v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                 v_RANKED_BYTES_PER_RING_ELEMENT == Spec.Kyber.v_RANKED_BYTES_PER_RING_ELEMENT p
                 ))
      (ensures (fun _ -> Prims.l_True))

val generate_keypair (#p:Spec.Kyber.params)
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
    : Pure (Libcrux.Kem.Kyber.Types.t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      (requires (v_K == p.v_RANK /\ v_ETA1 == p.v_ETA1 /\
                 v_ETA1_RANDOMNESS_SIZE == Spec.Kyber.v_ETA1_RANDOMNESS_SIZE p /\
                 v_PUBLIC_KEY_SIZE == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                 v_CPA_PRIVATE_KEY_SIZE == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                 v_PRIVATE_KEY_SIZE == Spec.Kyber.v_SECRET_KEY_SIZE p /\
                 v_BYTES_PER_RING_ELEMENT == Spec.Kyber.v_RANKED_BYTES_PER_RING_ELEMENT p
                 ))
      (ensures (fun kp -> 
                (kp.f_sk.f_value,kp.f_pk.f_value) == Spec.Kyber.ind_cca_generate_keypair p randomness))
