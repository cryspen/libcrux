module Libcrux_ml_kem.Ind_cca
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Types in
  let open Libcrux_ml_kem.Variant in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// Seed size for key generation
let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +!
  Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE

/// Seed size for encapsulation
let v_ENCAPS_SEED_SIZE: usize = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE

/// Serialize the secret key.
val serialize_kem_secret_key_mut
      (v_K v_SERIALIZED_KEY_LEN: usize)
      (#v_Hasher: Type0)
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (private_key public_key implicit_rejection_value: t_Slice u8)
      (serialized: t_Array u8 v_SERIALIZED_KEY_LEN)
    : Prims.Pure (t_Array u8 v_SERIALIZED_KEY_LEN)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_SERIALIZED_KEY_LEN == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K /\
        Core.Slice.impl__len #u8 private_key == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        Core.Slice.impl__len #u8 public_key == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        Core.Slice.impl__len #u8 implicit_rejection_value == Spec.MLKEM.v_SHARED_SECRET_SIZE)
      (ensures
        fun serialized_future ->
          let serialized_future:t_Array u8 v_SERIALIZED_KEY_LEN = serialized_future in
          serialized_future ==
          Seq.append private_key
            (Seq.append public_key (Seq.append (Spec.Utils.v_H public_key) implicit_rejection_value)
            ))

val serialize_kem_secret_key
      (v_K v_SERIALIZED_KEY_LEN: usize)
      (#v_Hasher: Type0)
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : Prims.Pure (t_Array u8 v_SERIALIZED_KEY_LEN)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_SERIALIZED_KEY_LEN == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K /\
        Core.Slice.impl__len #u8 private_key == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        Core.Slice.impl__len #u8 public_key == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        Core.Slice.impl__len #u8 implicit_rejection_value == Spec.MLKEM.v_SHARED_SECRET_SIZE)
      (ensures
        fun result ->
          let result:t_Array u8 v_SERIALIZED_KEY_LEN = result in
          result ==
          Seq.append private_key
            (Seq.append public_key (Seq.append (Spec.Utils.v_H public_key) implicit_rejection_value)
            ))

/// Validate an ML-KEM public key.
/// This implements the Modulus check in 7.2 2.
/// Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
/// `public_key` type.
val validate_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
    : Prims.Pure bool
      (requires
        Spec.MLKEM.is_rank v_K /\
        v_RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CCA_PUBLIC_KEY_SIZE v_K)
      (fun _ -> Prims.l_True)

/// Validate an ML-KEM private key.
/// This implements the Hash check in 7.3 3.
val validate_private_key_only
      (v_K v_SECRET_KEY_SIZE: usize)
      (#v_Hasher: Type0)
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
    : Prims.Pure bool
      (requires Spec.MLKEM.is_rank v_K /\ v_SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K
      )
      (fun _ -> Prims.l_True)

/// Validate an ML-KEM private key.
/// This implements the Hash check in 7.3 3.
/// Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
/// and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
val validate_private_key
      (v_K v_SECRET_KEY_SIZE v_CIPHERTEXT_SIZE: usize)
      (#v_Hasher: Type0)
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (v__ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    : Prims.Pure bool
      (requires
        Spec.MLKEM.is_rank v_K /\ v_SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K /\
        v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K)
      (fun _ -> Prims.l_True)

/// Packed API
/// Generate a key pair.
/// Depending on the `Vector` and `Hasher` used, this requires different hardware
/// features
val generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme |}
      (randomness: t_Array u8 (mk_usize 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_CPA_PRIVATE_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        v_PRIVATE_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        v_RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Types.t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
            result
          in
          let expected, valid = Spec.MLKEM.ind_cca_generate_keypair v_K randomness in
          valid ==> (result.f_sk.f_value, result.f_pk.f_value) == expected)

val encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme |}
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure
      (Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (mk_usize 32))
      (requires
        Spec.MLKEM.is_rank v_K /\ v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        v_T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K /\
        v_C1_SIZE == Spec.MLKEM.v_C1_SIZE v_K /\ v_C2_SIZE == Spec.MLKEM.v_C2_SIZE v_K /\
        v_VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        v_C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE v_K /\ v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA2 == Spec.MLKEM.v_ETA2 v_K /\
        v_ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE v_K)
      (ensures
        fun result ->
          let result:(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE &
            t_Array u8 (mk_usize 32)) =
            result
          in
          let expected, valid = Spec.MLKEM.ind_cca_encapsulate v_K public_key.f_value randomness in
          valid ==> (result._1.f_value, result._2) == expected)

/// This code verifies on some machines, runs out of memory on others
val decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme |}
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (mk_usize 32))
      (requires
        Spec.MLKEM.is_rank v_K /\ v_SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K /\
        v_CPA_SECRET_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K /\
        v_T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K /\
        v_C1_SIZE == Spec.MLKEM.v_C1_SIZE v_K /\ v_C2_SIZE == Spec.MLKEM.v_C2_SIZE v_K /\
        v_VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        v_C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE v_K /\ v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA2 == Spec.MLKEM.v_ETA2 v_K /\
        v_ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE v_K /\
        v_IMPLICIT_REJECTION_HASH_INPUT_SIZE == Spec.MLKEM.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE v_K)
      (ensures
        fun result ->
          let result:t_Array u8 (mk_usize 32) = result in
          let expected, valid =
            Spec.MLKEM.ind_cca_decapsulate v_K private_key.f_value ciphertext.f_value
          in
          valid ==> result == expected)
