module Libcrux_ml_kem.Ind_cca.Incremental.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Hash_functions.Portable in
  let open Libcrux_ml_kem.Vector.Portable in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let as_keypair (v_K: usize) (k: dyn 1 (fun z -> Core.Any.t_Any z)) =
  Core.Option.impl__unwrap #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    (Core.Any.impl_4__downcast_ref #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        k
      <:
      Core.Option.t_Option
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector))

let as_state (v_K: usize) (s: dyn 1 (fun z -> Core.Any.t_Any z)) =
  Core.Option.impl__unwrap #(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    (Core.Any.impl_4__downcast_ref #(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        s
      <:
      Core.Option.t_Option
      (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector))

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (mk_usize 64))
     =
  Libcrux_ml_kem.Ind_cca.Incremental.generate_keypair v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE
    v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE
    #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #(Libcrux_ml_kem.Hash_functions.Portable.t_PortableHash v_K) randomness

let generate_keypair_serialized
      (v_K v_PK2_LEN v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (mk_usize 64))
      (key_pair: t_Slice u8)
     =
  if
    (Core.Slice.impl__len #u8 key_pair <: usize) <.
    (Libcrux_ml_kem.Ind_cca.Incremental.Types.impl_15__num_bytes v_K
        v_PK2_LEN
        #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
        ()
      <:
      usize)
  then
    key_pair,
    (Core.Result.Result_Err
      (Libcrux_ml_kem.Ind_cca.Incremental.Types.Error_InvalidOutputLength
        <:
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
      <:
      Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
    <:
    (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
  else
    let tmp0, out:(t_Slice u8 &
      Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
      Libcrux_ml_kem.Ind_cca.Incremental.generate_keypair_serialized v_K v_PK2_LEN
        v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1
        v_ETA1_RANDOMNESS_SIZE #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
        #(Libcrux_ml_kem.Hash_functions.Portable.t_PortableHash v_K) randomness key_pair
    in
    let key_pair:t_Slice u8 = tmp0 in
    let hax_temp_output:Core.Result.t_Result Prims.unit
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error =
      out
    in
    key_pair, hax_temp_output
    <:
    (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)

let validate_pk
      (v_K v_PK_LEN: usize)
      (pk1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (pk2: t_Slice u8)
     =
  Libcrux_ml_kem.Ind_cca.Incremental.validate_pk v_K
    v_PK_LEN
    #(Libcrux_ml_kem.Hash_functions.Portable.t_PortableHash v_K)
    pk1
    pk2

let encapsulate1
      (v_K v_CIPHERTEXT_SIZE v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (randomness: t_Array u8 (mk_usize 32))
     =
  Libcrux_ml_kem.Ind_cca.Incremental.encapsulate1 v_K v_CIPHERTEXT_SIZE v_C1_SIZE
    v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
    v_ETA2_RANDOMNESS_SIZE #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #(Libcrux_ml_kem.Hash_functions.Portable.t_PortableHash v_K) public_key_part randomness

let encapsulate1_serialized
      (v_K v_CIPHERTEXT_SIZE v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (randomness: t_Array u8 (mk_usize 32))
      (state shared_secret: t_Slice u8)
     =
  let tmp0, tmp1, out:(t_Slice u8 & t_Slice u8 &
    Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
    Libcrux_ml_kem.Ind_cca.Incremental.encapsulate1_serialized v_K v_CIPHERTEXT_SIZE v_C1_SIZE
      v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
      v_ETA2_RANDOMNESS_SIZE #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #(Libcrux_ml_kem.Hash_functions.Portable.t_PortableHash v_K) public_key_part randomness state
      shared_secret
  in
  let state:t_Slice u8 = tmp0 in
  let shared_secret:t_Slice u8 = tmp1 in
  let hax_temp_output:Core.Result.t_Result
    (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
    Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error =
    out
  in
  state, shared_secret, hax_temp_output
  <:
  (t_Slice u8 & t_Slice u8 &
    Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)

let encapsulate2
      (v_K v_PK2_LEN v_C2_SIZE v_VECTOR_V_COMPRESSION_FACTOR: usize)
      (state:
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
     =
  Libcrux_ml_kem.Ind_cca.Incremental.encapsulate2 v_K
    v_PK2_LEN
    v_C2_SIZE
    v_VECTOR_V_COMPRESSION_FACTOR
    #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    state
    public_key_part

let encapsulate2_serialized
      (v_K v_PK2_LEN v_C2_SIZE v_VECTOR_V_COMPRESSION_FACTOR: usize)
      (state: t_Slice u8)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
     =
  Libcrux_ml_kem.Ind_cca.Incremental.encapsulate2_serialized v_K
    v_PK2_LEN
    v_C2_SIZE
    v_VECTOR_V_COMPRESSION_FACTOR
    #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    state
    public_key_part

let decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
     =
  Libcrux_ml_kem.Ind_cca.Incremental.decapsulate v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE
    v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE
    v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
    v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
    #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #(Libcrux_ml_kem.Hash_functions.Portable.t_PortableHash v_K) private_key ciphertext1 ciphertext2

let decapsulate_incremental_key
      (v_K v_PK2_LEN v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key: t_Slice u8)
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
     =
  Libcrux_ml_kem.Ind_cca.Incremental.decapsulate_incremental_key v_K v_PK2_LEN v_SECRET_KEY_SIZE
    v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
    v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
    v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
    #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #(Libcrux_ml_kem.Hash_functions.Portable.t_PortableHash v_K) private_key ciphertext1 ciphertext2
