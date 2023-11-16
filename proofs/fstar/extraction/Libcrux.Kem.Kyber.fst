module Libcrux.Kem.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_KyberSharedSecret = t_Array u8 (sz 32)

let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +!
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

let decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (secret_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : t_Array u8 (sz 32) =
  let ind_cpa_secret_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Libcrux.Kem.Kyber.Types.impl_18__split_at v_SECRET_KEY_SIZE secret_key v_CPA_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at secret_key v_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at secret_key Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
  in
  let decrypted:t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Ind_cpa.decrypt v_K
      v_CIPHERTEXT_SIZE
      v_C1_SIZE
      v_VECTOR_U_COMPRESSION_FACTOR
      v_VECTOR_V_COMPRESSION_FACTOR
      ind_cpa_secret_key
      ciphertext
  in
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (sz 64)
      (Rust_primitives.unsize decrypted <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice (to_hash.[ {
                Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
              }
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
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8)
      Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
  in
  let (to_hash: t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE):t_Array u8
    v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Libcrux.Kem.Kyber.Conversions.into_padded_array v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
      implicit_rejection_value
  in
  let to_hash:t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice (to_hash.[ {
                Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
              }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (Core.Convert.f_as_ref ciphertext <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let (implicit_rejection_shared_secret: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF (sz 32) (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let expected_ciphertext, _:(Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE ind_cpa_public_key decrypted
      pseudorandomness
  in
  let selector:u8 =
    Libcrux.Kem.Kyber.Constant_time_ops.compare_ciphertexts_in_constant_time v_CIPHERTEXT_SIZE
      (Core.Convert.f_as_ref ciphertext <: t_Slice u8)
      (Core.Convert.f_as_ref expected_ciphertext <: t_Slice u8)
  in
  Libcrux.Kem.Kyber.Constant_time_ops.select_shared_secret_in_constant_time shared_secret
    (Rust_primitives.unsize implicit_rejection_shared_secret <: t_Slice u8)
    selector

let encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
    : Core.Result.t_Result
      (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
      Libcrux.Kem.Kyber.Types.t_Error =
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (sz 64)
      (Rust_primitives.unsize randomness <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice (to_hash.[ {
                Core.Ops.Range.f_start = Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
              }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H (Rust_primitives.unsize (Libcrux.Kem.Kyber.Types.impl_24__as_slice
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
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8)
      Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
  in
  let ciphertext, sampling_a_error:(Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN
      v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE
      (Rust_primitives.unsize (Libcrux.Kem.Kyber.Types.impl_24__as_slice v_PUBLIC_KEY_SIZE
              public_key
            <:
            t_Array u8 v_PUBLIC_KEY_SIZE)
        <:
        t_Slice u8) randomness pseudorandomness
  in
  match sampling_a_error with
  | Core.Option.Option_Some e ->
    Core.Result.Result_Err e
    <:
    Core.Result.t_Result
      (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
      Libcrux.Kem.Kyber.Types.t_Error
  | Core.Option.Option_None  ->
    Core.Result.Result_Ok
    (ciphertext,
      Core.Result.impl__unwrap (Core.Convert.f_try_into shared_secret
          <:
          Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError)
      <:
      (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32)))
    <:
    Core.Result.t_Result
      (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
      Libcrux.Kem.Kyber.Types.t_Error

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64))
    : Core.Result.t_Result
      (Libcrux.Kem.Kyber.Types.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Libcrux.Kem.Kyber.Types.t_Error =
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
  let (ind_cpa_private_key, public_key), sampling_a_error:((Libcrux.Kem.Kyber.Types.t_PrivateKey
      v_CPA_PRIVATE_KEY_SIZE &
      Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
    Libcrux.Kem.Kyber.Ind_cpa.generate_keypair v_K
      v_CPA_PRIVATE_KEY_SIZE
      v_PUBLIC_KEY_SIZE
      v_BYTES_PER_RING_ELEMENT
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      ind_cpa_keypair_randomness
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.serialize_secret_key v_PRIVATE_KEY_SIZE
      (Rust_primitives.unsize (Libcrux.Kem.Kyber.Types.impl_30__as_slice v_CPA_PRIVATE_KEY_SIZE
              ind_cpa_private_key
            <:
            t_Array u8 v_CPA_PRIVATE_KEY_SIZE)
        <:
        t_Slice u8)
      (Rust_primitives.unsize (Libcrux.Kem.Kyber.Types.impl_24__as_slice v_PUBLIC_KEY_SIZE
              public_key
            <:
            t_Array u8 v_PUBLIC_KEY_SIZE)
        <:
        t_Slice u8)
      implicit_rejection_value
  in
  match sampling_a_error with
  | Core.Option.Option_Some error ->
    Core.Result.Result_Err error
    <:
    Core.Result.t_Result
      (Libcrux.Kem.Kyber.Types.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Libcrux.Kem.Kyber.Types.t_Error
  | _ ->
    let (private_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey v_PRIVATE_KEY_SIZE):Libcrux.Kem.Kyber.Types.t_KyberPrivateKey
    v_PRIVATE_KEY_SIZE =
      Core.Convert.f_from secret_key_serialized
    in
    Core.Result.Result_Ok
    (Libcrux.Kem.Kyber.Types.impl__from v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE private_key public_key)
    <:
    Core.Result.t_Result
      (Libcrux.Kem.Kyber.Types.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Libcrux.Kem.Kyber.Types.t_Error
