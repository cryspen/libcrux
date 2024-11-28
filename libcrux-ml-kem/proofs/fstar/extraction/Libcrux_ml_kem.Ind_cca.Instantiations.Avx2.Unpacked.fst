module Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Hash_functions.Avx2 in
  let open Libcrux_ml_kem.Variant in
  let open Libcrux_ml_kem.Vector.Avx2 in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let unpack_public_key_avx2
      (v_K v_T_AS_NTT_ENCODED_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (unpacked_public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
     =
  let hax_temp_output, unpacked_public_key:(Prims.unit &
    Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K
      Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector) =
    (),
    Libcrux_ml_kem.Ind_cca.Unpacked.unpack_public_key v_K
      v_T_AS_NTT_ENCODED_SIZE
      v_RANKED_BYTES_PER_RING_ELEMENT
      v_PUBLIC_KEY_SIZE
      #Libcrux_ml_kem.Hash_functions.Avx2.t_Simd256Hash
      #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector
      public_key
      unpacked_public_key
    <:
    (Prims.unit &
      Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K
        Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
  in
  unpacked_public_key

let unpack_public_key
      (v_K v_T_AS_NTT_ENCODED_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (unpacked_public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
     =
  let hax_temp_output, unpacked_public_key:(Prims.unit &
    Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K
      Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector) =
    (),
    unpack_public_key_avx2 v_K
      v_T_AS_NTT_ENCODED_SIZE
      v_RANKED_BYTES_PER_RING_ELEMENT
      v_PUBLIC_KEY_SIZE
      public_key
      unpacked_public_key
    <:
    (Prims.unit &
      Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K
        Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
  in
  unpacked_public_key

let keypair_from_private_key
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_T_AS_NTT_ENCODED_SIZE:
          usize)
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
     =
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
    Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector =
    Libcrux_ml_kem.Ind_cca.Unpacked.keys_from_private_key v_K
      v_SECRET_KEY_SIZE
      v_CPA_SECRET_KEY_SIZE
      v_PUBLIC_KEY_SIZE
      v_BYTES_PER_RING_ELEMENT
      v_T_AS_NTT_ENCODED_SIZE
      #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector
      private_key
      key_pair
  in
  key_pair

let generate_keypair_avx2
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
      (out:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
     =
  let hax_temp_output, out:(Prims.unit &
    Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
      Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector) =
    (),
    Libcrux_ml_kem.Ind_cca.Unpacked.generate_keypair v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE
      v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE
      #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector #Libcrux_ml_kem.Hash_functions.Avx2.t_Simd256Hash
      #Libcrux_ml_kem.Variant.t_MlKem randomness out
    <:
    (Prims.unit &
      Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
        Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
  in
  out

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
      (out:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
     =
  let hax_temp_output, out:(Prims.unit &
    Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
      Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector) =
    (),
    generate_keypair_avx2 v_K
      v_CPA_PRIVATE_KEY_SIZE
      v_PRIVATE_KEY_SIZE
      v_PUBLIC_KEY_SIZE
      v_BYTES_PER_RING_ELEMENT
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      randomness
      out
    <:
    (Prims.unit &
      Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
        Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
  in
  out

let encapsulate_avx2
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.Unpacked.encapsulate v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE
    v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
    v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
    v_ETA2_RANDOMNESS_SIZE #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector
    #Libcrux_ml_kem.Hash_functions.Avx2.t_Simd256Hash public_key randomness

let encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
      (randomness: t_Array u8 (sz 32))
     =
  encapsulate_avx2 v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
    v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN
    v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE public_key randomness

let decapsulate_avx2
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  Libcrux_ml_kem.Ind_cca.Unpacked.decapsulate v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE
    v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE
    v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
    v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
    #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector #Libcrux_ml_kem.Hash_functions.Avx2.t_Simd256Hash
    key_pair ciphertext

let decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  decapsulate_avx2 v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE
    v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
    v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
    v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE key_pair ciphertext
