module Libcrux.Kem.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux.Kem.Kyber.Types in
  ()

let serialize_kem_secret_key
      (v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: t_Slice u8)
     =
  let out:t_Array u8 v_SERIALIZED_KEY_LEN = Rust_primitives.Hax.repeat 0uy v_SERIALIZED_KEY_LEN in
  let pointer:usize = sz 0 in
  let out:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end = pointer +! (Core.Slice.impl__len #u8 private_key <: usize) <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (out.[ {
                Core.Ops.Range.f_start = pointer;
                Core.Ops.Range.f_end
                =
                pointer +! (Core.Slice.impl__len #u8 private_key <: usize) <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          private_key
        <:
        t_Slice u8)
  in
  let pointer:usize = pointer +! (Core.Slice.impl__len #u8 private_key <: usize) in
  let out:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end = pointer +! (Core.Slice.impl__len #u8 public_key <: usize) <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (out.[ {
                Core.Ops.Range.f_start = pointer;
                Core.Ops.Range.f_end
                =
                pointer +! (Core.Slice.impl__len #u8 public_key <: usize) <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          public_key
        <:
        t_Slice u8)
  in
  let pointer:usize = pointer +! (Core.Slice.impl__len #u8 public_key <: usize) in
  let out:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end = pointer +! Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (out.[ {
                Core.Ops.Range.f_start = pointer;
                Core.Ops.Range.f_end
                =
                pointer +! Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H public_key
                <:
                t_Array u8 (sz 32))
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let pointer:usize = pointer +! Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE in
  let out:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end
          =
          pointer +! (Core.Slice.impl__len #u8 implicit_rejection_value <: usize) <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (out.[ {
                Core.Ops.Range.f_start = pointer;
                Core.Ops.Range.f_end
                =
                pointer +! (Core.Slice.impl__len #u8 implicit_rejection_value <: usize) <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          implicit_rejection_value
        <:
        t_Slice u8)
  in
  out

let decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (secret_key: Libcrux.Kem.Kyber.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  let ind_cpa_secret_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Libcrux.Kem.Kyber.Types.impl_12__split_at v_SECRET_KEY_SIZE secret_key v_CPA_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 secret_key v_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 secret_key Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
  in
  let decrypted:t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Ind_cpa.decrypt v_K
      v_CIPHERTEXT_SIZE
      v_C1_SIZE
      v_VECTOR_U_COMPRESSION_FACTOR
      v_VECTOR_V_COMPRESSION_FACTOR
      ind_cpa_secret_key
      ciphertext.Libcrux.Kem.Kyber.Types.f_value
  in
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Ind_cpa.into_padded_array (sz 64)
      (Rust_primitives.unsize decrypted <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          ind_cpa_public_key_hash
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (Rust_primitives.unsize hashed <: t_Slice u8)
      Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
  in
  let (to_hash: t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE):t_Array u8
    v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.into_padded_array v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
      implicit_rejection_value
  in
  let to_hash:t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (Core.Convert.f_as_ref #(Libcrux.Kem.Kyber.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
              #(t_Slice u8)
              ciphertext
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let (implicit_rejection_shared_secret: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF (sz 32) (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let expected_ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE ind_cpa_public_key decrypted
      pseudorandomness
  in
  let selector:u8 =
    Libcrux.Kem.Kyber.Constant_time_ops.compare_ciphertexts_in_constant_time v_CIPHERTEXT_SIZE
      (Core.Convert.f_as_ref #(Libcrux.Kem.Kyber.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
          #(t_Slice u8)
          ciphertext
        <:
        t_Slice u8)
      (Rust_primitives.unsize expected_ciphertext <: t_Slice u8)
  in
  Libcrux.Kem.Kyber.Constant_time_ops.select_shared_secret_in_constant_time shared_secret
    (Rust_primitives.unsize implicit_rejection_shared_secret <: t_Slice u8)
    selector

let encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: Libcrux.Kem.Kyber.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
     =
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Ind_cpa.into_padded_array (sz 64)
      (Rust_primitives.unsize randomness <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H (Rust_primitives.unsize (Libcrux.Kem.Kyber.Types.impl_18__as_slice
                          v_PUBLIC_KEY_SIZE
                          public_key
                        <:
                        t_Array u8 v_PUBLIC_KEY_SIZE)
                    <:
                    t_Slice u8)
                <:
                t_Array u8 (sz 32))
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (Rust_primitives.unsize hashed <: t_Slice u8)
      Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN
      v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE
      (Rust_primitives.unsize (Libcrux.Kem.Kyber.Types.impl_18__as_slice v_PUBLIC_KEY_SIZE
              public_key
            <:
            t_Array u8 v_PUBLIC_KEY_SIZE)
        <:
        t_Slice u8) randomness pseudorandomness
  in
  let shared_secret_array:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let shared_secret_array:t_Array u8 (sz 32) =
    Core.Slice.impl__copy_from_slice #u8 shared_secret_array shared_secret
  in
  Core.Convert.f_into #(t_Array u8 v_CIPHERTEXT_SIZE)
    #(Libcrux.Kem.Kyber.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    ciphertext,
  shared_secret_array
  <:
  (Libcrux.Kem.Kyber.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))

let validate_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
     =
  let deserialized_pk:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Serialize.deserialize_ring_elements_reduced v_PUBLIC_KEY_SIZE
      v_K
      (public_key.[ { Core.Ops.Range.f_end = v_RANKED_BYTES_PER_RING_ELEMENT }
          <:
          Core.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8)
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.serialize_public_key v_K
      v_RANKED_BYTES_PER_RING_ELEMENT
      v_PUBLIC_KEY_SIZE
      deserialized_pk
      (public_key.[ { Core.Ops.Range.f_start = v_RANKED_BYTES_PER_RING_ELEMENT }
          <:
          Core.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  public_key =. public_key_serialized

let decapsulate_unpacked
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (state: t_MlKemState v_K)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  let (secret_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K):t_Array
    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    state.f_secret_as_ntt
  in
  let (tt_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K):t_Array
    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    state.f_t_as_ntt
  in
  let (a_transpose: t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K):t_Array
    (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K =
    state.f_a_transpose
  in
  let (implicit_rejection_value: t_Slice u8):t_Slice u8 = Rust_primitives.unsize state.f_rej in
  let (ind_cpa_public_key_hash: t_Slice u8):t_Slice u8 =
    Rust_primitives.unsize state.f_ind_cpa_public_key_hash
  in
  let decrypted:t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Ind_cpa.decrypt_unpacked v_K
      v_CIPHERTEXT_SIZE
      v_C1_SIZE
      v_VECTOR_U_COMPRESSION_FACTOR
      v_VECTOR_V_COMPRESSION_FACTOR
      secret_as_ntt
      ciphertext.Libcrux.Kem.Kyber.Types.f_value
  in
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Ind_cpa.into_padded_array (sz 64)
      (Rust_primitives.unsize decrypted <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          ind_cpa_public_key_hash
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (Rust_primitives.unsize hashed <: t_Slice u8)
      Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
  in
  let (to_hash: t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE):t_Array u8
    v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.into_padded_array v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
      implicit_rejection_value
  in
  let to_hash:t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (Core.Convert.f_as_ref #(Libcrux.Kem.Kyber.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
              #(t_Slice u8)
              ciphertext
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let (implicit_rejection_shared_secret: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF (sz 32) (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let expected_ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt_unpacked v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE
      v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR
      v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE tt_as_ntt
      a_transpose decrypted pseudorandomness
  in
  let selector:u8 =
    Libcrux.Kem.Kyber.Constant_time_ops.compare_ciphertexts_in_constant_time v_CIPHERTEXT_SIZE
      (Core.Convert.f_as_ref #(Libcrux.Kem.Kyber.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
          #(t_Slice u8)
          ciphertext
        <:
        t_Slice u8)
      (Rust_primitives.unsize expected_ciphertext <: t_Slice u8)
  in
  Libcrux.Kem.Kyber.Constant_time_ops.select_shared_secret_in_constant_time shared_secret
    (Rust_primitives.unsize implicit_rejection_shared_secret <: t_Slice u8)
    selector

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
     =
  let ind_cpa_keypair_randomness:t_Slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = sz 0;
        Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      }
      <:
      Core.Ops.Range.t_Range usize ]
  in
  let implicit_rejection_value:t_Slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      }
      <:
      Core.Ops.Range.t_RangeFrom usize ]
  in
  let ind_cpa_private_key, public_key:(t_Array u8 v_CPA_PRIVATE_KEY_SIZE &
    t_Array u8 v_PUBLIC_KEY_SIZE) =
    Libcrux.Kem.Kyber.Ind_cpa.generate_keypair v_K
      v_CPA_PRIVATE_KEY_SIZE
      v_PUBLIC_KEY_SIZE
      v_BYTES_PER_RING_ELEMENT
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      ind_cpa_keypair_randomness
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    serialize_kem_secret_key v_PRIVATE_KEY_SIZE
      (Rust_primitives.unsize ind_cpa_private_key <: t_Slice u8)
      (Rust_primitives.unsize public_key <: t_Slice u8)
      implicit_rejection_value
  in
  let (private_key: Libcrux.Kem.Kyber.Types.t_MlKemPrivateKey v_PRIVATE_KEY_SIZE):Libcrux.Kem.Kyber.Types.t_MlKemPrivateKey
  v_PRIVATE_KEY_SIZE =
    Core.Convert.f_from #(Libcrux.Kem.Kyber.Types.t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      #(t_Array u8 v_PRIVATE_KEY_SIZE)
      secret_key_serialized
  in
  Libcrux.Kem.Kyber.Types.impl__from v_PRIVATE_KEY_SIZE
    v_PUBLIC_KEY_SIZE
    private_key
    (Core.Convert.f_into #(t_Array u8 v_PUBLIC_KEY_SIZE)
        #(Libcrux.Kem.Kyber.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
        public_key
      <:
      Libcrux.Kem.Kyber.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)

let generate_keypair_unpacked
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
     =
  let ind_cpa_keypair_randomness:t_Slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = sz 0;
        Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      }
      <:
      Core.Ops.Range.t_Range usize ]
  in
  let implicit_rejection_value:t_Slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      }
      <:
      Core.Ops.Range.t_RangeFrom usize ]
  in
  let (secret_as_ntt, tt_as_ntt, a_transpose), ind_cpa_public_key:((t_Array
        Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K &
      t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K &
      t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K) &
    t_Array u8 v_PUBLIC_KEY_SIZE) =
    Libcrux.Kem.Kyber.Ind_cpa.generate_keypair_unpacked v_K
      v_PUBLIC_KEY_SIZE
      v_BYTES_PER_RING_ELEMENT
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      ind_cpa_keypair_randomness
  in
  let ind_cpa_public_key_hash:t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Hash_functions.v_H (Rust_primitives.unsize ind_cpa_public_key <: t_Slice u8)
  in
  let (rej: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Core.Result.impl__unwrap #(t_Array u8 (sz 32))
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice u8) #(t_Array u8 (sz 32)) implicit_rejection_value
        <:
        Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError)
  in
  let (pubkey: Libcrux.Kem.Kyber.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE):Libcrux.Kem.Kyber.Types.t_MlKemPublicKey
  v_PUBLIC_KEY_SIZE =
    Core.Convert.f_from #(Libcrux.Kem.Kyber.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      #(t_Array u8 v_PUBLIC_KEY_SIZE)
      ind_cpa_public_key
  in
  ({
      f_secret_as_ntt = secret_as_ntt;
      f_t_as_ntt = tt_as_ntt;
      f_a_transpose = a_transpose;
      f_rej = rej;
      f_ind_cpa_public_key_hash = ind_cpa_public_key_hash
    }
    <:
    t_MlKemState v_K),
  pubkey
  <:
  (t_MlKemState v_K & Libcrux.Kem.Kyber.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
