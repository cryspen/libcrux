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

let serialize_kem_secret_key
      (v_K v_SERIALIZED_KEY_LEN: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
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
          Core.Ops.Range.f_end = pointer +! Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (out.[ {
                Core.Ops.Range.f_start = pointer;
                Core.Ops.Range.f_end = pointer +! Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (Libcrux_ml_kem.Hash_functions.f_H #v_Hasher
              #v_K
              #FStar.Tactics.Typeclasses.solve
              public_key
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let pointer:usize = pointer +! Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE in
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

let validate_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
     =
  let deserialized_pk:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Libcrux_ml_kem.Serialize.deserialize_ring_elements_reduced_out v_PUBLIC_KEY_SIZE
      v_K
      #v_Vector
      (public_key.[ { Core.Ops.Range.f_end = v_RANKED_BYTES_PER_RING_ELEMENT }
          <:
          Core.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8)
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Libcrux_ml_kem.Ind_cpa.serialize_public_key v_K
      v_RANKED_BYTES_PER_RING_ELEMENT
      v_PUBLIC_KEY_SIZE
      #v_Vector
      deserialized_pk
      (public_key.[ { Core.Ops.Range.f_start = v_RANKED_BYTES_PER_RING_ELEMENT }
          <:
          Core.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  public_key =. public_key_serialized

let validate_private_key
      (v_K v_SECRET_KEY_SIZE v_CIPHERTEXT_SIZE: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (v__ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  let t:t_Array u8 (sz 32) =
    Libcrux_ml_kem.Hash_functions.f_H #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      (private_key.Libcrux_ml_kem.Types.f_value.[ {
            Core.Ops.Range.f_start = sz 384 *! v_K <: usize;
            Core.Ops.Range.f_end = (sz 768 *! v_K <: usize) +! sz 32 <: usize
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let expected:t_Slice u8 =
    private_key.Libcrux_ml_kem.Types.f_value.[ {
        Core.Ops.Range.f_start = (sz 768 *! v_K <: usize) +! sz 32 <: usize;
        Core.Ops.Range.f_end = (sz 768 *! v_K <: usize) +! sz 64 <: usize
      }
      <:
      Core.Ops.Range.t_Range usize ]
  in
  t =. expected

let decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme)
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  let ind_cpa_secret_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (private_key.Libcrux_ml_kem.Types.f_value <: t_Slice u8)
      v_CPA_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 secret_key v_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 secret_key Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE
  in
  let decrypted:t_Array u8 (sz 32) =
    Libcrux_ml_kem.Ind_cpa.decrypt v_K
      v_CIPHERTEXT_SIZE
      v_C1_SIZE
      v_VECTOR_U_COMPRESSION_FACTOR
      v_VECTOR_V_COMPRESSION_FACTOR
      #v_Vector
      ind_cpa_secret_key
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
          ind_cpa_public_key_hash
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
      implicit_rejection_value
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
    Libcrux_ml_kem.Ind_cpa.encrypt v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE
      v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE #v_Vector #v_Hasher ind_cpa_public_key
      decrypted pseudorandomness
  in
  let implicit_rejection_shared_secret:t_Array u8 (sz 32) =
    Libcrux_ml_kem.Variant.f_kdf #v_Scheme
      #FStar.Tactics.Typeclasses.solve
      v_K
      v_CIPHERTEXT_SIZE
      #v_Hasher
      (implicit_rejection_shared_secret <: t_Slice u8)
      ciphertext
  in
  let shared_secret:t_Array u8 (sz 32) =
    Libcrux_ml_kem.Variant.f_kdf #v_Scheme
      #FStar.Tactics.Typeclasses.solve
      v_K
      v_CIPHERTEXT_SIZE
      #v_Hasher
      shared_secret
      ciphertext
  in
  Libcrux_ml_kem.Constant_time_ops.compare_ciphertexts_select_shared_secret_in_constant_time (Core.Convert.f_as_ref
        #(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
        #(t_Slice u8)
        #FStar.Tactics.Typeclasses.solve
        ciphertext
      <:
      t_Slice u8)
    (expected_ciphertext <: t_Slice u8)
    (shared_secret <: t_Slice u8)
    (implicit_rejection_shared_secret <: t_Slice u8)

let encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme)
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
     =
  let randomness:t_Array u8 (sz 32) =
    Libcrux_ml_kem.Variant.f_entropy_preprocess #v_Scheme
      #FStar.Tactics.Typeclasses.solve
      v_K
      #v_Hasher
      (randomness <: t_Slice u8)
  in
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
          (Libcrux_ml_kem.Hash_functions.f_H #v_Hasher
              #v_K
              #FStar.Tactics.Typeclasses.solve
              (Libcrux_ml_kem.Types.impl_21__as_slice v_PUBLIC_KEY_SIZE public_key <: t_Slice u8)
            <:
            t_Slice u8)
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
    Libcrux_ml_kem.Ind_cpa.encrypt v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE
      v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE #v_Vector #v_Hasher
      (Libcrux_ml_kem.Types.impl_21__as_slice v_PUBLIC_KEY_SIZE public_key <: t_Slice u8) randomness
      pseudorandomness
  in
  let ciphertext:Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE =
    Core.Convert.f_from #(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
      #(t_Array u8 v_CIPHERTEXT_SIZE)
      #FStar.Tactics.Typeclasses.solve
      ciphertext
  in
  let shared_secret_array:t_Array u8 (sz 32) =
    Libcrux_ml_kem.Variant.f_kdf #v_Scheme
      #FStar.Tactics.Typeclasses.solve
      v_K
      v_CIPHERTEXT_SIZE
      #v_Hasher
      shared_secret
      ciphertext
  in
  ciphertext, shared_secret_array
  <:
  (Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme)
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
  let ind_cpa_private_key, public_key:(t_Array u8 v_CPA_PRIVATE_KEY_SIZE &
    t_Array u8 v_PUBLIC_KEY_SIZE) =
    Libcrux_ml_kem.Ind_cpa.generate_keypair v_K v_CPA_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE
      v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE #v_Vector #v_Hasher #v_Scheme
      ind_cpa_keypair_randomness
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    serialize_kem_secret_key v_K
      v_PRIVATE_KEY_SIZE
      #v_Hasher
      (ind_cpa_private_key <: t_Slice u8)
      (public_key <: t_Slice u8)
      implicit_rejection_value
  in
  let (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_PRIVATE_KEY_SIZE):Libcrux_ml_kem.Types.t_MlKemPrivateKey
  v_PRIVATE_KEY_SIZE =
    Core.Convert.f_from #(Libcrux_ml_kem.Types.t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      #(t_Array u8 v_PRIVATE_KEY_SIZE)
      #FStar.Tactics.Typeclasses.solve
      secret_key_serialized
  in
  Libcrux_ml_kem.Types.impl__from v_PRIVATE_KEY_SIZE
    v_PUBLIC_KEY_SIZE
    private_key
    (Core.Convert.f_from #(Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
        #(t_Array u8 v_PUBLIC_KEY_SIZE)
        #FStar.Tactics.Typeclasses.solve
        public_key
      <:
      Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
