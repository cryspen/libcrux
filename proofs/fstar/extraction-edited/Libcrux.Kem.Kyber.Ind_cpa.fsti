module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val serialize_secret_key
      (v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : t_Array u8 v_SERIALIZED_KEY_LEN

val decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (secret_key: t_Slice u8)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : t_Array u8 (sz 32)

val encrypt
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8{length randomness <. sz 33})
    : (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)

val generate_keypair
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (key_generation_seed: t_Slice u8)
    : ((Libcrux.Kem.Kyber.Types.t_PrivateKey v_PRIVATE_KEY_SIZE &
        Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)
