module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val into_padded_array (v_LEN: usize) (slice: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

val sample_ring_element_cbd
      (v_K v_ETA2_RANDOMNESS_SIZE v_ETA2: usize)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : Prims.Pure
      (t_Array u8 (sz 33) & u8 & t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_vector_cbd_then_ntt
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : Prims.Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K & u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val compress_then_serialize_u
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (input: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_then_decompress_u
      (v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR: usize)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_public_key (v_K: usize) (public_key: t_Slice u8)
    : Prims.Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_secret_key (v_K: usize) (secret_key: t_Slice u8)
    : Prims.Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val encrypt
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8)
    : Prims.Pure (t_Array u8 v_CIPHERTEXT_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val serialize_secret_key
      (v_K v_OUT_LEN: usize)
      (key: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val serialize_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (tt_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (seed_for_a: t_Slice u8)
    : Prims.Pure (t_Array u8 v_PUBLIC_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val generate_keypair
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (key_generation_seed: t_Slice u8)
    : Prims.Pure (t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)
