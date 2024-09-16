module Libcrux_ml_kem.Ind_cca.Instantiations.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions.Avx2 in
  let open Libcrux_ml_kem.Variant in
  let open Libcrux_ml_kem.Vector.Avx2 in
  ()

let validate_private_key
      (v_K v_SECRET_KEY_SIZE v_CIPHERTEXT_SIZE: usize)
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  Libcrux_ml_kem.Ind_cca.validate_private_key v_K
    v_SECRET_KEY_SIZE
    v_CIPHERTEXT_SIZE
    #Libcrux_ml_kem.Hash_functions.Avx2.t_Simd256Hash
    private_key
    ciphertext

let validate_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
     =
  Libcrux_ml_kem.Ind_cca.validate_public_key v_K
    v_RANKED_BYTES_PER_RING_ELEMENT
    v_PUBLIC_KEY_SIZE
    #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector
    public_key

let decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  Libcrux_ml_kem.Ind_cca.decapsulate v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE
    v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
    v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
    v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
    #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector #Libcrux_ml_kem.Hash_functions.Avx2.t_Simd256Hash
    #Libcrux_ml_kem.Variant.t_MlKem private_key ciphertext

let encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.encapsulate v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE
    v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR
    v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE
    #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector #Libcrux_ml_kem.Hash_functions.Avx2.t_Simd256Hash
    #Libcrux_ml_kem.Variant.t_MlKem public_key randomness

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
     =
  Libcrux_ml_kem.Ind_cca.generate_keypair v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE
    v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE
    #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector #Libcrux_ml_kem.Hash_functions.Avx2.t_Simd256Hash
    #Libcrux_ml_kem.Variant.t_MlKem randomness
