module Libcrux_ml_kem.Ind_cca.Multiplexing
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let validate_private_key
      (v_K v_SECRET_KEY_SIZE v_CIPHERTEXT_SIZE: usize)
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.validate_private_key v_K
    v_SECRET_KEY_SIZE
    v_CIPHERTEXT_SIZE
    private_key
    ciphertext

let validate_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.validate_public_key v_K
    v_RANKED_BYTES_PER_RING_ELEMENT
    v_PUBLIC_KEY_SIZE
    public_key

let decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.decapsulate v_K v_SECRET_KEY_SIZE
      v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
      private_key ciphertext
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_kem.Ind_cca.Instantiations.Neon.decapsulate v_K v_SECRET_KEY_SIZE
        v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
        v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
        v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
        private_key ciphertext
    else
      Libcrux_ml_kem.Ind_cca.Instantiations.Portable.decapsulate v_K v_SECRET_KEY_SIZE
        v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
        v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
        v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
        private_key ciphertext

let encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.encapsulate v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE
      v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
      v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
      v_ETA2_RANDOMNESS_SIZE public_key randomness
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_kem.Ind_cca.Instantiations.Neon.encapsulate v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE
        v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
        v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
        v_ETA2_RANDOMNESS_SIZE public_key randomness
    else
      Libcrux_ml_kem.Ind_cca.Instantiations.Portable.encapsulate v_K v_CIPHERTEXT_SIZE
        v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
        v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
        v_ETA2_RANDOMNESS_SIZE public_key randomness

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.generate_keypair v_K
      v_CPA_PRIVATE_KEY_SIZE
      v_PRIVATE_KEY_SIZE
      v_PUBLIC_KEY_SIZE
      v_BYTES_PER_RING_ELEMENT
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      randomness
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_kem.Ind_cca.Instantiations.Neon.generate_keypair v_K
        v_CPA_PRIVATE_KEY_SIZE
        v_PRIVATE_KEY_SIZE
        v_PUBLIC_KEY_SIZE
        v_BYTES_PER_RING_ELEMENT
        v_ETA1
        v_ETA1_RANDOMNESS_SIZE
        randomness
    else
      Libcrux_ml_kem.Ind_cca.Instantiations.Portable.generate_keypair v_K
        v_CPA_PRIVATE_KEY_SIZE
        v_PRIVATE_KEY_SIZE
        v_PUBLIC_KEY_SIZE
        v_BYTES_PER_RING_ELEMENT
        v_ETA1
        v_ETA1_RANDOMNESS_SIZE
        randomness
