module Libcrux_ml_kem.Ind_cca
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
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

/// Seed size for encapsulation
let v_ENCAPS_SEED_SIZE: usize = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE

/// Seed size for key generation
let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +!
  Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE

/// Serialize the secret key.
val serialize_kem_secret_key
      (v_K v_SERIALIZED_KEY_LEN: usize)
      (#v_Hasher: Type0)
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : Prims.Pure (t_Array u8 v_SERIALIZED_KEY_LEN) Prims.l_True (fun _ -> Prims.l_True)

/// Validate an ML-KEM public key.
/// This implements the Modulus check in 7.2 2.
/// Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
/// `public_key` type.
val validate_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

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
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme |}
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme |}
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Packed API
/// Generate a key pair.
/// Depending on the `Vector` and `Hasher` used, this requires different hardware
/// features
val generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme |}
      (randomness: t_Array u8 (sz 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)
