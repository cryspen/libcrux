module Libcrux_ml_kem.Ind_cca.Incremental.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Hash_functions.Neon in
  let open Libcrux_ml_kem.Vector.Neon in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// Downcast [`Keys`] to a platform dependent [`MlKemKeyPairUnpacked`].
/// **PANICS** is the cast fails
val as_keypair (v_K: usize) (k: dyn 1 (fun z -> Core.Any.t_Any z))
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
          Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Downcast [`State`] to a  platform dependent [`EncapsState`].
/// **PANICS** is the cast fails
val as_state (v_K: usize) (s: dyn 1 (fun z -> Core.Any.t_Any z))
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
          Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

val generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (mk_usize 64))
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
          Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

val generate_keypair_serialized
      (v_K v_PK2_LEN v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (mk_usize 64))
      (key_pair: t_Slice u8)
    : Prims.Pure
      (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
      ) Prims.l_True (fun _ -> Prims.l_True)

val validate_pk
      (v_K v_PK_LEN: usize)
      (pk1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (pk2: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

val encapsulate1
      (v_K v_CIPHERTEXT_SIZE v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE &
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
          Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector &
        t_Array u8 (mk_usize 32)) Prims.l_True (fun _ -> Prims.l_True)

val encapsulate1_serialized
      (v_K v_CIPHERTEXT_SIZE v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (randomness: t_Array u8 (mk_usize 32))
      (state shared_secret: t_Slice u8)
    : Prims.Pure
      (t_Slice u8 & t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) Prims.l_True (fun _ -> Prims.l_True)

val encapsulate2
      (v_K v_PK2_LEN v_C2_SIZE v_VECTOR_V_COMPRESSION_FACTOR: usize)
      (state:
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
    : Prims.Pure (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

val encapsulate2_serialized
      (v_K v_PK2_LEN v_C2_SIZE v_VECTOR_V_COMPRESSION_FACTOR: usize)
      (state: t_Slice u8)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) Prims.l_True (fun _ -> Prims.l_True)

val decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
    : Prims.Pure (t_Array u8 (mk_usize 32)) Prims.l_True (fun _ -> Prims.l_True)

val decapsulate_incremental_key
      (v_K v_PK2_LEN v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key: t_Slice u8)
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
    : Prims.Pure
      (Core.Result.t_Result (t_Array u8 (mk_usize 32))
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) Prims.l_True (fun _ -> Prims.l_True)
