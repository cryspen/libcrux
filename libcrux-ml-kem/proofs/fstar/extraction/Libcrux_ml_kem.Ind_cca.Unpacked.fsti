module Libcrux_ml_kem.Ind_cca.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Polynomial in
  let open Libcrux_ml_kem.Types in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// An unpacked ML-KEM IND-CCA Private Key
type t_MlKemPrivateKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_ind_cpa_private_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector;
  f_implicit_rejection_value:t_Array u8 (sz 32)
}

/// An unpacked ML-KEM IND-CCA Private Key
type t_MlKemPublicKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_ind_cpa_public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector;
  f_public_key_hash:t_Array u8 (sz 32)
}

val encapsulate_unpacked
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (public_key: t_MlKemPublicKeyUnpacked v_K v_Vector)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// An unpacked ML-KEM KeyPair
type t_MlKemKeyPairUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_private_key:t_MlKemPrivateKeyUnpacked v_K v_Vector;
  f_public_key:t_MlKemPublicKeyUnpacked v_K v_Vector
}

val decapsulate_unpacked
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (key_pair: t_MlKemKeyPairUnpacked v_K v_Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val generate_keypair_unpacked
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (randomness: t_Array u8 (sz 64))
    : Prims.Pure (t_MlKemKeyPairUnpacked v_K v_Vector) Prims.l_True (fun _ -> Prims.l_True)
