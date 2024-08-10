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

let encapsulate_unpacked
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (public_key: t_MlKemPublicKeyUnpacked v_K v_Vector)
      (randomness: t_Array u8 (sz 32))
     =
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux_ml_kem.Utils.into_padded_array (sz 64) (randomness <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (public_key.f_public_key_hash <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (sz 64) =
    Libcrux_ml_kem.Hash_functions.f_G #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      (to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (hashed <: t_Slice u8)
      Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux_ml_kem.Ind_cpa.encrypt_unpacked v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN
      v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE #v_Vector #v_Hasher
      public_key.f_ind_cpa_public_key randomness pseudorandomness
  in
  let shared_secret_array:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let shared_secret_array:t_Array u8 (sz 32) =
    Core.Slice.impl__copy_from_slice #u8 shared_secret_array shared_secret
  in
  Core.Convert.f_from #(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    #(t_Array u8 v_CIPHERTEXT_SIZE)
    #FStar.Tactics.Typeclasses.solve
    ciphertext,
  shared_secret_array
  <:
  (Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))

let decapsulate_unpacked
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (key_pair: t_MlKemKeyPairUnpacked v_K v_Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  let decrypted:t_Array u8 (sz 32) =
    Libcrux_ml_kem.Ind_cpa.decrypt_unpacked v_K
      v_CIPHERTEXT_SIZE
      v_C1_SIZE
      v_VECTOR_U_COMPRESSION_FACTOR
      v_VECTOR_V_COMPRESSION_FACTOR
      #v_Vector
      key_pair.f_private_key.f_ind_cpa_private_key
      ciphertext.Libcrux_ml_kem.Types.f_value
  in
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux_ml_kem.Utils.into_padded_array (sz 64) (decrypted <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (key_pair.f_public_key.f_public_key_hash <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (sz 64) =
    Libcrux_ml_kem.Hash_functions.f_G #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      (to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (hashed <: t_Slice u8)
      Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE
  in
  let (to_hash: t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE):t_Array u8
    v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Libcrux_ml_kem.Utils.into_padded_array v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
      (key_pair.f_private_key.f_implicit_rejection_value <: t_Slice u8)
  in
  let to_hash:t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (Core.Convert.f_as_ref #(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
              #(t_Slice u8)
              #FStar.Tactics.Typeclasses.solve
              ciphertext
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let (implicit_rejection_shared_secret: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Libcrux_ml_kem.Hash_functions.f_PRF #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      (sz 32)
      (to_hash <: t_Slice u8)
  in
  let expected_ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux_ml_kem.Ind_cpa.encrypt_unpacked v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE #v_Vector #v_Hasher
      key_pair.f_public_key.f_ind_cpa_public_key decrypted pseudorandomness
  in
  let selector:u8 =
    Libcrux_ml_kem.Constant_time_ops.compare_ciphertexts_in_constant_time (Core.Convert.f_as_ref #(Libcrux_ml_kem.Types.t_MlKemCiphertext
            v_CIPHERTEXT_SIZE)
          #(t_Slice u8)
          #FStar.Tactics.Typeclasses.solve
          ciphertext
        <:
        t_Slice u8)
      (expected_ciphertext <: t_Slice u8)
  in
  Libcrux_ml_kem.Constant_time_ops.select_shared_secret_in_constant_time shared_secret
    (implicit_rejection_shared_secret <: t_Slice u8)
    selector

let generate_keypair_unpacked
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (randomness: t_Array u8 (sz 64))
     =
  let ind_cpa_keypair_randomness:t_Slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = sz 0;
        Core.Ops.Range.f_end = Libcrux_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      }
      <:
      Core.Ops.Range.t_Range usize ]
  in
  let implicit_rejection_value:t_Slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      }
      <:
      Core.Ops.Range.t_RangeFrom usize ]
  in
  let ind_cpa_private_key, ind_cpa_public_key:(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked
      v_K v_Vector &
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector) =
    Libcrux_ml_kem.Ind_cpa.generate_keypair_unpacked v_K
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      #v_Vector
      #v_Hasher
      ind_cpa_keypair_randomness
  in
  let v_A:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
    Core.Array.from_fn #(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      v_K
      (fun v__i ->
          let v__i:usize = v__i in
          Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
            v_K
            (fun v__j ->
                let v__j:usize = v__j in
                Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          <:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
  in
  let v_A:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          #FStar.Tactics.Typeclasses.solve
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v_A
      (fun v_A i ->
          let v_A:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
            v_K =
            v_A
          in
          let i:usize = i in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                  usize)
                #FStar.Tactics.Typeclasses.solve
                ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Core.Ops.Range.t_Range usize)
            v_A
            (fun v_A j ->
                let v_A:t_Array
                  (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
                  v_A
                in
                let j:usize = j in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
                  i
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ i ]
                        <:
                        t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                      j
                      (Core.Clone.f_clone #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
                            v_Vector)
                          #FStar.Tactics.Typeclasses.solve
                          ((ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_A.[ j ]
                              <:
                              t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                                v_K).[ i ]
                            <:
                            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                        <:
                        Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    <:
                    t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                <:
                t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                  v_K)
          <:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
  in
  let ind_cpa_public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    { ind_cpa_public_key with Libcrux_ml_kem.Ind_cpa.Unpacked.f_A = v_A }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
  in
  let pk_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Libcrux_ml_kem.Ind_cpa.serialize_public_key v_K
      v_BYTES_PER_RING_ELEMENT
      v_PUBLIC_KEY_SIZE
      #v_Vector
      ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
      (ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A <: t_Slice u8)
  in
  let public_key_hash:t_Array u8 (sz 32) =
    Libcrux_ml_kem.Hash_functions.f_H #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      (pk_serialized <: t_Slice u8)
  in
  let (implicit_rejection_value: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Core.Result.impl__unwrap #(t_Array u8 (sz 32))
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice u8)
          #(t_Array u8 (sz 32))
          #FStar.Tactics.Typeclasses.solve
          implicit_rejection_value
        <:
        Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError)
  in
  {
    f_private_key
    =
    {
      f_ind_cpa_private_key = ind_cpa_private_key;
      f_implicit_rejection_value = implicit_rejection_value
    }
    <:
    t_MlKemPrivateKeyUnpacked v_K v_Vector;
    f_public_key
    =
    { f_ind_cpa_public_key = ind_cpa_public_key; f_public_key_hash = public_key_hash }
    <:
    t_MlKemPublicKeyUnpacked v_K v_Vector
  }
  <:
  t_MlKemKeyPairUnpacked v_K v_Vector
