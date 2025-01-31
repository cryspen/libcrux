module Libcrux_ml_kem.Ind_cca.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Ind_cca.Incremental.Types in
  let open Libcrux_ml_kem.Types in
  let open Libcrux_ml_kem.Variant in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (randomness: t_Array u8 (mk_usize 64))
     =
  let kp:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__new v_K #v_Vector ()
  in
  let kp:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector =
    Libcrux_ml_kem.Ind_cca.Unpacked.generate_keypair v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE
      v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE #v_Vector #v_Hasher
      #Libcrux_ml_kem.Variant.t_MlKem randomness kp
  in
  kp

let generate_keypair_serialized
      (v_K v_PK2_LEN v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (randomness: t_Array u8 (mk_usize 64))
      (key_pair: t_Slice u8)
     =
  let kp:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__new v_K #v_Vector ()
  in
  let kp:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector =
    Libcrux_ml_kem.Ind_cca.Unpacked.generate_keypair v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE
      v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE #v_Vector #v_Hasher
      #Libcrux_ml_kem.Variant.t_MlKem randomness kp
  in
  let kp:Libcrux_ml_kem.Ind_cca.Incremental.Types.t_KeyPair v_K v_PK2_LEN v_Vector =
    Core.Convert.f_from #(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_KeyPair v_K v_PK2_LEN v_Vector)
      #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
      #FStar.Tactics.Typeclasses.solve
      kp
  in
  let tmp0, out:(t_Slice u8 &
    Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
    Libcrux_ml_kem.Ind_cca.Incremental.Types.impl_15__to_bytes v_K v_PK2_LEN #v_Vector kp key_pair
  in
  let key_pair:t_Slice u8 = tmp0 in
  let hax_temp_output:Core.Result.t_Result Prims.unit
    Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error =
    out
  in
  key_pair, hax_temp_output
  <:
  (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)

let encapsulate1
      (v_K v_CIPHERTEXT_SIZE v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (pk1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (randomness: t_Array u8 (mk_usize 32))
     =
  let hashed:t_Array u8 (mk_usize 64) =
    Libcrux_ml_kem.Ind_cca.Unpacked.encaps_prepare v_K
      #v_Hasher
      (randomness <: t_Slice u8)
      (pk1.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (hashed <: t_Slice u8)
      Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE
  in
  let matrix:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K
  =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (Libcrux_ml_kem.Polynomial.impl_2__ZERO #v_Vector
              ()
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          v_K
        <:
        t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      v_K
  in
  let matrix:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K
  =
    Libcrux_ml_kem.Matrix.sample_matrix_A v_K
      #v_Vector
      #v_Hasher
      matrix
      (Libcrux_ml_kem.Utils.into_padded_array (mk_usize 34)
          (pk1.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_seed <: t_Slice u8)
        <:
        t_Array u8 (mk_usize 34))
      false
  in
  let ciphertext:t_Array u8 v_C1_SIZE = Rust_primitives.Hax.repeat (mk_u8 0) v_C1_SIZE in
  let tmp0, out:(t_Array u8 v_C1_SIZE &
    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
      Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)) =
    Libcrux_ml_kem.Ind_cpa.encrypt_c1 v_K v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR
      v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE #v_Vector
      #v_Hasher pseudorandomness matrix ciphertext
  in
  let ciphertext:t_Array u8 v_C1_SIZE = tmp0 in
  let r_as_ntt, error2:(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
    Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    out
  in
  let state:Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K v_Vector =
    {
      Libcrux_ml_kem.Ind_cca.Incremental.Types.f_randomness = randomness;
      Libcrux_ml_kem.Ind_cca.Incremental.Types.f_r_as_ntt = r_as_ntt;
      Libcrux_ml_kem.Ind_cca.Incremental.Types.f_error2 = error2
    }
    <:
    Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K v_Vector
  in
  ({ Libcrux_ml_kem.Ind_cca.Incremental.Types.f_value = ciphertext }
    <:
    Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE),
  state,
  Core.Result.impl__unwrap #(t_Array u8 (mk_usize 32))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (mk_usize 32))
        #FStar.Tactics.Typeclasses.solve
        shared_secret
      <:
      Core.Result.t_Result (t_Array u8 (mk_usize 32)) Core.Array.t_TryFromSliceError)
  <:
  (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE &
    Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K v_Vector &
    t_Array u8 (mk_usize 32))

let encapsulate1_serialized
      (v_K v_CIPHERTEXT_SIZE v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (pk1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (randomness: t_Array u8 (mk_usize 32))
      (state shared_secret: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 shared_secret <: usize) >=.
            Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE
            <:
            bool)
      in
      ()
  in
  if
    (Core.Slice.impl__len #u8 shared_secret <: usize) <.
    Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE
  then
    state,
    shared_secret,
    (Core.Result.Result_Err
      (Libcrux_ml_kem.Ind_cca.Incremental.Types.Error_InvalidOutputLength
        <:
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
      <:
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
    <:
    (t_Slice u8 & t_Slice u8 &
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
  else
    let ct1, encaps_state, ss:(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE &
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K v_Vector &
      t_Array u8 (mk_usize 32)) =
      encapsulate1 v_K v_CIPHERTEXT_SIZE v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR
        v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE #v_Vector
        #v_Hasher pk1 randomness
    in
    let tmp0, out:(t_Slice u8 &
      Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
      Libcrux_ml_kem.Ind_cca.Incremental.Types.impl_8__to_bytes v_K #v_Vector encaps_state state
    in
    let state:t_Slice u8 = tmp0 in
    match
      out <: Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
    with
    | Core.Result.Result_Ok _ ->
      let shared_secret:t_Slice u8 =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to shared_secret
          ({ Core.Ops.Range.f_end = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE }
            <:
            Core.Ops.Range.t_RangeTo usize)
          (Core.Slice.impl__copy_from_slice #u8
              (shared_secret.[ {
                    Core.Ops.Range.f_end = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE
                  }
                  <:
                  Core.Ops.Range.t_RangeTo usize ]
                <:
                t_Slice u8)
              (ss <: t_Slice u8)
            <:
            t_Slice u8)
      in
      let hax_temp_output:Core.Result.t_Result
        (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error =
        Core.Result.Result_Ok ct1
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
      in
      state, shared_secret, hax_temp_output
      <:
      (t_Slice u8 & t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
    | Core.Result.Result_Err err ->
      state,
      shared_secret,
      (Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
      <:
      (t_Slice u8 & t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)

let validate_pk
      (v_K v_PK_LEN: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (pk1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (pk2: t_Slice u8)
     =
  let pk:t_Array u8 v_PK_LEN = Rust_primitives.Hax.repeat (mk_u8 0) v_PK_LEN in
  let pk2_len:usize =
    (v_K *! Libcrux_ml_kem.Constants.v_BITS_PER_RING_ELEMENT <: usize) /! mk_usize 8
  in
  let pk:t_Array u8 v_PK_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range pk
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = pk2_len }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (pk.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = pk2_len }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          pk2
        <:
        t_Slice u8)
  in
  let pk:t_Array u8 v_PK_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from pk
      ({ Core.Ops.Range.f_start = pk2_len } <: Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (pk.[ { Core.Ops.Range.f_start = pk2_len } <: Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (pk1.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_seed <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let hash:t_Array u8 (mk_usize 32) =
    Libcrux_ml_kem.Hash_functions.f_H #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      (pk <: t_Slice u8)
  in
  if hash <>. pk1.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_hash
  then
    Core.Result.Result_Err
    (Libcrux_ml_kem.Ind_cca.Incremental.Types.Error_InvalidPublicKey
      <:
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
    <:
    Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
  else
    Core.Result.Result_Ok (() <: Prims.unit)
    <:
    Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error

let encapsulate2
      (v_K v_PK2_LEN v_C2_SIZE v_VECTOR_V_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (state: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K v_Vector)
      (pk2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
     =
  let ciphertext:t_Array u8 v_C2_SIZE = Rust_primitives.Hax.repeat (mk_u8 0) v_C2_SIZE in
  let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Libcrux_ml_kem.Ind_cca.Incremental.Types.impl_4__deserialize v_PK2_LEN v_K #v_Vector pk2
  in
  let ciphertext:t_Array u8 v_C2_SIZE =
    Libcrux_ml_kem.Ind_cpa.encrypt_c2 v_K
      v_VECTOR_V_COMPRESSION_FACTOR
      v_C2_SIZE
      #v_Vector
      tt_as_ntt
      state.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_r_as_ntt
      state.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_error2
      state.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_randomness
      ciphertext
  in
  { Libcrux_ml_kem.Ind_cca.Incremental.Types.f_value = ciphertext }
  <:
  Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE

let encapsulate2_serialized
      (v_K v_PK2_LEN v_C2_SIZE v_VECTOR_V_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (state: t_Slice u8)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
     =
  match
    Libcrux_ml_kem.Ind_cca.Incremental.Types.impl_8__from_bytes v_K #v_Vector state
    <:
    Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K v_Vector)
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
  with
  | Core.Result.Result_Ok state ->
    Core.Result.Result_Ok
    (encapsulate2 v_K
        v_PK2_LEN
        v_C2_SIZE
        v_VECTOR_V_COMPRESSION_FACTOR
        #v_Vector
        state
        public_key_part)
    <:
    Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error

let decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (private_key: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
     =
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.repeat (mk_u8 0) v_CIPHERTEXT_SIZE
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to ciphertext
      ({ Core.Ops.Range.f_end = v_C1_SIZE } <: Core.Ops.Range.t_RangeTo usize)
      (Core.Slice.impl__copy_from_slice #u8
          (ciphertext.[ { Core.Ops.Range.f_end = v_C1_SIZE } <: Core.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
          (ciphertext1.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_value <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from ciphertext
      ({ Core.Ops.Range.f_start = v_C1_SIZE } <: Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (ciphertext.[ { Core.Ops.Range.f_start = v_C1_SIZE } <: Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (ciphertext2.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_value <: t_Slice u8)
        <:
        t_Slice u8)
  in
  Libcrux_ml_kem.Ind_cca.Unpacked.decapsulate v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE
    v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE
    v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
    v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
    #v_Vector #v_Hasher private_key
    (Core.Convert.f_into #(t_Array u8 v_CIPHERTEXT_SIZE)
        #(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
        #FStar.Tactics.Typeclasses.solve
        ciphertext
      <:
      Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)

let decapsulate_incremental_key
      (v_K v_PK2_LEN v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (key: t_Slice u8)
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
     =
  match
    Libcrux_ml_kem.Ind_cca.Incremental.Types.impl_15__from_bytes v_K v_PK2_LEN #v_Vector key
    <:
    Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_KeyPair v_K v_PK2_LEN v_Vector)
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
  with
  | Core.Result.Result_Ok
    (key_pair: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_KeyPair v_K v_PK2_LEN v_Vector) ->
    let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
      Rust_primitives.Hax.repeat (mk_u8 0) v_CIPHERTEXT_SIZE
    in
    let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to ciphertext
        ({ Core.Ops.Range.f_end = v_C1_SIZE } <: Core.Ops.Range.t_RangeTo usize)
        (Core.Slice.impl__copy_from_slice #u8
            (ciphertext.[ { Core.Ops.Range.f_end = v_C1_SIZE } <: Core.Ops.Range.t_RangeTo usize ]
              <:
              t_Slice u8)
            (ciphertext1.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_value <: t_Slice u8)
          <:
          t_Slice u8)
    in
    let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from ciphertext
        ({ Core.Ops.Range.f_start = v_C1_SIZE } <: Core.Ops.Range.t_RangeFrom usize)
        (Core.Slice.impl__copy_from_slice #u8
            (ciphertext.[ { Core.Ops.Range.f_start = v_C1_SIZE } <: Core.Ops.Range.t_RangeFrom usize
              ]
              <:
              t_Slice u8)
            (ciphertext2.Libcrux_ml_kem.Ind_cca.Incremental.Types.f_value <: t_Slice u8)
          <:
          t_Slice u8)
    in
    Core.Result.Result_Ok
    (Libcrux_ml_kem.Ind_cca.Unpacked.decapsulate v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE
        v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE
        v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
        v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
        #v_Vector #v_Hasher
        (Core.Convert.f_into #(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_KeyPair v_K
                v_PK2_LEN
                v_Vector)
            #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
            #FStar.Tactics.Typeclasses.solve
            key_pair
          <:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
        (Core.Convert.f_into #(t_Array u8 v_CIPHERTEXT_SIZE)
            #(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
            #FStar.Tactics.Typeclasses.solve
            ciphertext
          <:
          Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE))
    <:
    Core.Result.t_Result (t_Array u8 (mk_usize 32)) Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (t_Array u8 (mk_usize 32)) Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
