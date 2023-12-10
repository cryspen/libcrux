module Libcrux.Kem.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

unfold
let t_KyberSharedSecret = t_Array u8 (sz 32)

let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux.Kem.Kyber.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +!
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

val serialize_kem_secret_key (#p:Spec.Kyber.params)
      (v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : Pure (t_Array u8 v_SERIALIZED_KEY_LEN)
      (requires (length private_key == Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p /\
                 length public_key == Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p /\
                 length implicit_rejection_value == Spec.Kyber.v_SHARED_SECRET_SIZE /\
                 v_SERIALIZED_KEY_LEN == Spec.Kyber.v_SECRET_KEY_SIZE p))
      (ensures (fun res -> res ==
                Seq.append private_key (
                Seq.append public_key (
                Seq.append (Libcrux.Kem.Kyber.Hash_functions.v_H public_key) implicit_rejection_value))))
                


let serialize_kem_secret_key #p
      (v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: t_Slice u8) =
  let out:t_Array u8 v_SERIALIZED_KEY_LEN = Rust_primitives.Hax.repeat 0uy v_SERIALIZED_KEY_LEN in
  let pointer:usize = sz 0 in
  let out:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end = pointer +! (Core.Slice.impl__len private_key <: usize) <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice (out.[ {
                Core.Ops.Range.f_start = pointer;
                Core.Ops.Range.f_end
                =
                pointer +! (Core.Slice.impl__len private_key <: usize) <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          private_key
        <:
        t_Slice u8)
  in
  assert (Seq.slice out 0 (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p)) == private_key);
  let pointer:usize = pointer +! (Core.Slice.impl__len private_key <: usize) in
  let out:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end = pointer +! (Core.Slice.impl__len public_key <: usize) <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice (out.[ {
                Core.Ops.Range.f_start = pointer;
                Core.Ops.Range.f_end
                =
                pointer +! (Core.Slice.impl__len public_key <: usize) <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          public_key
        <:
        t_Slice u8)
  in
  assert (Seq.slice out 0 (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p)) == private_key);
  assert (Seq.slice out (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p))
                        (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p +!
                                           Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p))
          == public_key);

  let pointer:usize = pointer +! (Core.Slice.impl__len public_key <: usize) in
  let h_public_key = (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H public_key)
                     <: t_Slice u8) in

  let out:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end = pointer +! Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice (out.[ {
                Core.Ops.Range.f_start = pointer;
                Core.Ops.Range.f_end
                =
                pointer +! Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]) h_public_key)
  in
  assume (Seq.slice out 0 (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p)) == private_key);
  assume (Seq.slice out (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p))
                        (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p +! Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p)) == public_key);
  assert (Seq.slice out (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p +!
                                           Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p))
                        (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p +!
                                           Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p +!
                                           Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE))
          == Libcrux.Kem.Kyber.Hash_functions.v_H public_key);
  let pointer:usize = pointer +! Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE in
  let out:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end
          =
          pointer +! (Core.Slice.impl__len implicit_rejection_value <: usize) <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice (out.[ {
                Core.Ops.Range.f_start = pointer;
                Core.Ops.Range.f_end
                =
                pointer +! (Core.Slice.impl__len implicit_rejection_value <: usize) <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          implicit_rejection_value
        <:
        t_Slice u8)
  in
  assume (Seq.slice out 0 (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p)) == private_key);
  assume (Seq.slice out (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p))
                        (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p +! Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p)) == public_key);
  assume (Seq.slice out (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p +!
                                           Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p))
                        (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p +!
                                           Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p +!
                                           Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE))
          == Libcrux.Kem.Kyber.Hash_functions.v_H public_key);
  assert (Seq.slice out (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p +!
                                           Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p +!
                                           Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE))
                        (v #usize_inttype (Spec.Kyber.v_CPA_PKE_SECRET_KEY_SIZE p +!
                                           Spec.Kyber.v_CPA_PKE_PUBLIC_KEY_SIZE p +!
                                           Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE +!
                                           Spec.Kyber.v_SHARED_SECRET_SIZE))
          == implicit_rejection_value);
  Spec.Kyber.lemma_slice_append_4 out private_key public_key (Libcrux.Kem.Kyber.Hash_functions.v_H public_key) implicit_rejection_value;
  out

let decapsulate #p
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (secret_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE) =
  let orig_secret_key = secret_key.f_value in
  let ind_cpa_secret_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Libcrux.Kem.Kyber.Types.impl_12__split_at v_SECRET_KEY_SIZE secret_key v_CPA_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at secret_key v_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at secret_key Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
  in
  assert (ind_cpa_secret_key == Spec.Kyber.slice orig_secret_key (sz 0) v_CPA_SECRET_KEY_SIZE);
  assert (ind_cpa_public_key == Spec.Kyber.slice orig_secret_key v_CPA_SECRET_KEY_SIZE (v_CPA_SECRET_KEY_SIZE +! v_PUBLIC_KEY_SIZE));
  assert (ind_cpa_public_key_hash == Spec.Kyber.slice orig_secret_key (v_CPA_SECRET_KEY_SIZE +! v_PUBLIC_KEY_SIZE) (v_CPA_SECRET_KEY_SIZE +! v_PUBLIC_KEY_SIZE +! Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE));
  assert (implicit_rejection_value == Spec.Kyber.slice orig_secret_key (v_CPA_SECRET_KEY_SIZE +! v_PUBLIC_KEY_SIZE +! Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE) (length orig_secret_key));
  let decrypted:t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Ind_cpa.decrypt #p v_K
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
  Spec.Kyber.lemma_slice_append to_hash decrypted ind_cpa_public_key_hash;
  assert (decrypted == Spec.Kyber.ind_cpa_decrypt p ind_cpa_secret_key ciphertext.f_value);
  assert (to_hash == Spec.Kyber.concat decrypted ind_cpa_public_key_hash);
  let hashed:t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8)
      Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
  in
  assert ((shared_secret,pseudorandomness) == Spec.Kyber.split hashed Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE);
  assert (length implicit_rejection_value = v_SECRET_KEY_SIZE -! v_CPA_SECRET_KEY_SIZE -! v_PUBLIC_KEY_SIZE -! Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE);
  assert (length implicit_rejection_value = Spec.Kyber.v_SHARED_SECRET_SIZE);
  assert (Spec.Kyber.v_SHARED_SECRET_SIZE <=. Spec.Kyber.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE p);
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
  Spec.Kyber.lemma_slice_append to_hash implicit_rejection_value ciphertext.f_value;
  let (implicit_rejection_shared_secret: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF (sz 32) (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  assert (implicit_rejection_shared_secret == Spec.Kyber.v_J to_hash);
  let expected_ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt #p v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE ind_cpa_public_key decrypted
      pseudorandomness
  in
  let selector:u8 =
    Libcrux.Kem.Kyber.Constant_time_ops.compare_ciphertexts_in_constant_time v_CIPHERTEXT_SIZE
      (Core.Convert.f_as_ref ciphertext <: t_Slice u8)
      (Rust_primitives.unsize expected_ciphertext <: t_Slice u8)
  in
  let res = 
  Libcrux.Kem.Kyber.Constant_time_ops.select_shared_secret_in_constant_time shared_secret
    (Rust_primitives.unsize implicit_rejection_shared_secret <: t_Slice u8)
    selector
  in
  res

let encapsulate #p
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32)) =
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Ind_cpa.into_padded_array (sz 64)
      (Rust_primitives.unsize randomness <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
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
  assert (Seq.slice to_hash 0 (v Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE) == randomness);
  Spec.Kyber.lemma_slice_append to_hash randomness (Spec.Kyber.v_H public_key.f_value);
  assert (to_hash == Spec.Kyber.concat randomness (Spec.Kyber.v_H public_key.f_value));

  let hashed:t_Array u8 (sz 64) =
    Libcrux.Kem.Kyber.Hash_functions.v_G (Rust_primitives.unsize to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8)
      Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux.Kem.Kyber.Ind_cpa.encrypt #p v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN
      v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE
      (Rust_primitives.unsize (Libcrux.Kem.Kyber.Types.impl_18__as_slice v_PUBLIC_KEY_SIZE
              public_key
            <:
            t_Array u8 v_PUBLIC_KEY_SIZE)
        <:
        t_Slice u8) randomness pseudorandomness
  in
  Core.Convert.f_into ciphertext,
  Core.Result.impl__unwrap (Core.Convert.f_try_into shared_secret
      <:
      Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError)
  <:
  (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))

let generate_keypair #p
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (sz 64)) =
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
    Libcrux.Kem.Kyber.Ind_cpa.generate_keypair #p v_K
      v_CPA_PRIVATE_KEY_SIZE
      v_PUBLIC_KEY_SIZE
      v_BYTES_PER_RING_ELEMENT
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      ind_cpa_keypair_randomness
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    serialize_kem_secret_key #p v_PRIVATE_KEY_SIZE
      (Rust_primitives.unsize ind_cpa_private_key <: t_Slice u8)
      (Rust_primitives.unsize public_key <: t_Slice u8)
      implicit_rejection_value
  in
  let (private_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey v_PRIVATE_KEY_SIZE):Libcrux.Kem.Kyber.Types.t_KyberPrivateKey
  v_PRIVATE_KEY_SIZE =
    Core.Convert.f_from secret_key_serialized
  in
  Libcrux.Kem.Kyber.Types.impl__from v_PRIVATE_KEY_SIZE
    v_PUBLIC_KEY_SIZE
    private_key
    (Core.Convert.f_into public_key <: Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE)

