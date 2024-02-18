module Libcrux.Kem.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_KyberSharedSecret = t_Array u8 (sz 32)

let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +!
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

val serialize_kem_secret_key
      (v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : Prims.Pure (t_Array u8 v_SERIALIZED_KEY_LEN) Prims.l_True (fun _ -> Prims.l_True)

val decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (secret_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
    : Prims.Pure (Libcrux.Kem.Kyber.Types.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)
