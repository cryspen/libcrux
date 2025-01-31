module Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cca.Incremental.Types in
  ()

let generate_keypair
      (v_K v_PK2_LEN v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (mk_usize 64))
      (key_pair: t_Slice u8)
     =
  let key_pair, hax_temp_output:(t_Slice u8 &
    Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
    if Libcrux_platform.Platform.simd256_support ()
    then
      let tmp0, out:(t_Slice u8 &
        Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
        Libcrux_ml_kem.Ind_cca.Incremental.Avx2.generate_keypair_serialized v_K v_PK2_LEN
          v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT
          v_ETA1 v_ETA1_RANDOMNESS_SIZE randomness key_pair
      in
      let key_pair:t_Slice u8 = tmp0 in
      key_pair, out
      <:
      (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
      )
    else
      if Libcrux_platform.Platform.simd128_support ()
      then
        let tmp0, out:(t_Slice u8 &
          Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
          Libcrux_ml_kem.Ind_cca.Incremental.Neon.generate_keypair_serialized v_K v_PK2_LEN
            v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT
            v_ETA1 v_ETA1_RANDOMNESS_SIZE randomness key_pair
        in
        let key_pair:t_Slice u8 = tmp0 in
        key_pair, out
        <:
        (t_Slice u8 &
          Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
      else
        let tmp0, out:(t_Slice u8 &
          Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
          Libcrux_ml_kem.Ind_cca.Incremental.Portable.generate_keypair_serialized v_K v_PK2_LEN
            v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT
            v_ETA1 v_ETA1_RANDOMNESS_SIZE randomness key_pair
        in
        let key_pair:t_Slice u8 = tmp0 in
        key_pair, out
        <:
        (t_Slice u8 &
          Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
  in
  key_pair, hax_temp_output
  <:
  (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)

let validate_pk
      (v_K v_PK_LEN: usize)
      (pk1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (pk2: t_Slice u8)
     =
  if Libcrux_platform.Platform.simd256_support ()
  then Libcrux_ml_kem.Ind_cca.Incremental.Avx2.validate_pk v_K v_PK_LEN pk1 pk2
  else
    if Libcrux_platform.Platform.simd128_support ()
    then Libcrux_ml_kem.Ind_cca.Incremental.Neon.validate_pk v_K v_PK_LEN pk1 pk2
    else Libcrux_ml_kem.Ind_cca.Incremental.Portable.validate_pk v_K v_PK_LEN pk1 pk2

let encapsulate1
      (v_K v_CIPHERTEXT_SIZE v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (randomness: t_Array u8 (mk_usize 32))
      (state shared_secret: t_Slice u8)
     =
  let (shared_secret, state), hax_temp_output:((t_Slice u8 & t_Slice u8) &
    Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
    if Libcrux_platform.Platform.simd256_support ()
    then
      let tmp0, tmp1, out:(t_Slice u8 & t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
        Libcrux_ml_kem.Ind_cca.Incremental.Avx2.encapsulate1_serialized v_K v_CIPHERTEXT_SIZE
          v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE
          v_ETA2 v_ETA2_RANDOMNESS_SIZE public_key_part randomness state shared_secret
      in
      let state:t_Slice u8 = tmp0 in
      let shared_secret:t_Slice u8 = tmp1 in
      (shared_secret, state <: (t_Slice u8 & t_Slice u8)), out
      <:
      ((t_Slice u8 & t_Slice u8) &
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
    else
      if Libcrux_platform.Platform.simd128_support ()
      then
        let tmp0, tmp1, out:(t_Slice u8 & t_Slice u8 &
          Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
            Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
          Libcrux_ml_kem.Ind_cca.Incremental.Neon.encapsulate1_serialized v_K v_CIPHERTEXT_SIZE
            v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1
            v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE public_key_part randomness state
            shared_secret
        in
        let state:t_Slice u8 = tmp0 in
        let shared_secret:t_Slice u8 = tmp1 in
        (shared_secret, state <: (t_Slice u8 & t_Slice u8)), out
        <:
        ((t_Slice u8 & t_Slice u8) &
          Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
            Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
      else
        let tmp0, tmp1, out:(t_Slice u8 & t_Slice u8 &
          Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
            Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
          Libcrux_ml_kem.Ind_cca.Incremental.Portable.encapsulate1_serialized v_K v_CIPHERTEXT_SIZE
            v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1
            v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE public_key_part randomness state
            shared_secret
        in
        let state:t_Slice u8 = tmp0 in
        let shared_secret:t_Slice u8 = tmp1 in
        (shared_secret, state <: (t_Slice u8 & t_Slice u8)), out
        <:
        ((t_Slice u8 & t_Slice u8) &
          Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
            Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
  in
  state, shared_secret, hax_temp_output
  <:
  (t_Slice u8 & t_Slice u8 &
    Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)

let encapsulate2
      (v_K v_PK2_LEN v_C2_SIZE v_VECTOR_V_COMPRESSION_FACTOR: usize)
      (state public_key_part: t_Slice u8)
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    match
      Core.Convert.f_try_from #(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
        #(t_Slice u8)
        #FStar.Tactics.Typeclasses.solve
        public_key_part
      <:
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
    with
    | Core.Result.Result_Ok pk2 ->
      Libcrux_ml_kem.Ind_cca.Incremental.Avx2.encapsulate2_serialized v_K
        v_PK2_LEN
        v_C2_SIZE
        v_VECTOR_V_COMPRESSION_FACTOR
        state
        pk2
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err
      <:
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      match
        Core.Convert.f_try_from #(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
          #(t_Slice u8)
          #FStar.Tactics.Typeclasses.solve
          public_key_part
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
      with
      | Core.Result.Result_Ok pk2 ->
        Libcrux_ml_kem.Ind_cca.Incremental.Neon.encapsulate2_serialized v_K
          v_PK2_LEN
          v_C2_SIZE
          v_VECTOR_V_COMPRESSION_FACTOR
          state
          pk2
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
    else
      match
        Core.Convert.f_try_from #(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
          #(t_Slice u8)
          #FStar.Tactics.Typeclasses.solve
          public_key_part
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
      with
      | Core.Result.Result_Ok pk2 ->
        Libcrux_ml_kem.Ind_cca.Incremental.Portable.encapsulate2_serialized v_K
          v_PK2_LEN
          v_C2_SIZE
          v_VECTOR_V_COMPRESSION_FACTOR
          state
          pk2
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error

let decapsulate
      (v_K v_PK2_LEN v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key: t_Slice u8)
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_kem.Ind_cca.Incremental.Avx2.decapsulate_incremental_key v_K v_PK2_LEN
      v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE
      v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
      v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
      v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE private_key ciphertext1
      ciphertext2
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_kem.Ind_cca.Incremental.Neon.decapsulate_incremental_key v_K v_PK2_LEN
        v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE
        v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
        v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
        v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE private_key ciphertext1
        ciphertext2
    else
      Libcrux_ml_kem.Ind_cca.Incremental.Portable.decapsulate_incremental_key v_K v_PK2_LEN
        v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE
        v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
        v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
        v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE private_key ciphertext1
        ciphertext2
