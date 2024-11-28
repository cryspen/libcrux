module Libcrux_ml_kem.Ind_cca
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
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

#push-options "--z3rlimit 300"

let validate_private_key_only
      (v_K v_SECRET_KEY_SIZE: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
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

#pop-options

#push-options "--z3rlimit 300"

let validate_private_key
      (v_K v_SECRET_KEY_SIZE v_CIPHERTEXT_SIZE: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (v__ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     = validate_private_key_only v_K v_SECRET_KEY_SIZE #v_Hasher private_key

#pop-options

#push-options "--z3rlimit 150"

let serialize_kem_secret_key_mut
      (v_K v_SERIALIZED_KEY_LEN: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (private_key public_key implicit_rejection_value: t_Slice u8)
      (serialized: t_Array u8 v_SERIALIZED_KEY_LEN)
     =
  let pointer:usize = sz 0 in
  let serialized:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end = pointer +! (Core.Slice.impl__len #u8 private_key <: usize) <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized.[ {
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
  let serialized:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end = pointer +! (Core.Slice.impl__len #u8 public_key <: usize) <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized.[ {
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
  let serialized:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end = pointer +! Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized.[ {
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
  let serialized:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = pointer;
          Core.Ops.Range.f_end
          =
          pointer +! (Core.Slice.impl__len #u8 implicit_rejection_value <: usize) <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized.[ {
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
  let _:Prims.unit =
    let open Spec.Utils in
    assert ((Seq.slice serialized 0 (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K)))
        `Seq.equal`
        private_key);
    assert ((Seq.slice serialized
            (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K))
            (v #usize_inttype
                (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K +! Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K)))
        `Seq.equal`
        public_key);
    assert ((Seq.slice serialized
            (v #usize_inttype
                (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K +! Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K))
            (v #usize_inttype
                (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K +! Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K +!
                  Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE)))
        `Seq.equal`
        (Libcrux_ml_kem.Hash_functions.f_H #v_Hasher #v_K public_key));
    assert (Seq.slice serialized
          (v #usize_inttype
              (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K +! Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K +!
                Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE))
          (v #usize_inttype
              (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K +! Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K +!
                Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE +!
                Spec.MLKEM.v_SHARED_SECRET_SIZE)) ==
        implicit_rejection_value);
    lemma_slice_append_4 serialized
      private_key
      public_key
      (Libcrux_ml_kem.Hash_functions.f_H #v_Hasher #v_K public_key)
      implicit_rejection_value
  in
  serialized

#pop-options

#push-options "--z3rlimit 150"

let serialize_kem_secret_key
      (v_K v_SERIALIZED_KEY_LEN: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (private_key public_key implicit_rejection_value: t_Slice u8)
     =
  let out:t_Array u8 v_SERIALIZED_KEY_LEN = Rust_primitives.Hax.repeat 0uy v_SERIALIZED_KEY_LEN in
  let out:t_Array u8 v_SERIALIZED_KEY_LEN =
    serialize_kem_secret_key_mut v_K
      v_SERIALIZED_KEY_LEN
      #v_Hasher
      private_key
      public_key
      implicit_rejection_value
      out
  in
  out

#pop-options

#push-options "--z3rlimit 300"

let encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
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
  let _:Prims.unit = eq_intro (Seq.slice to_hash 0 32) randomness in
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
              (Libcrux_ml_kem.Types.impl_20__as_slice v_PUBLIC_KEY_SIZE public_key <: t_Slice u8)
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let _:Prims.unit =
    assert (Seq.slice to_hash 0 (v Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE) == randomness);
    lemma_slice_append to_hash randomness (Spec.Utils.v_H public_key.f_value);
    assert (to_hash == concat randomness (Spec.Utils.v_H public_key.f_value))
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
      v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE #v_Vector #v_Hasher
      (Libcrux_ml_kem.Types.impl_20__as_slice v_PUBLIC_KEY_SIZE public_key <: t_Slice u8) randomness
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
  let result:(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32)) =
    ciphertext, shared_secret_array
    <:
    (Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

#pop-options

let validate_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
     =
  let deserialized_pk:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Libcrux_ml_kem.Serialize.deserialize_ring_elements_reduced_out v_K
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

#push-options "--z3rlimit 300"

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
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
      v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE #v_Vector #v_Hasher #v_Scheme
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
  let result:Libcrux_ml_kem.Types.t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
    Libcrux_ml_kem.Types.impl_21__from v_PRIVATE_KEY_SIZE
      v_PUBLIC_KEY_SIZE
      private_key
      (Core.Convert.f_from #(Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
          #(t_Array u8 v_PUBLIC_KEY_SIZE)
          #FStar.Tactics.Typeclasses.solve
          public_key
        <:
        Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

#pop-options

#push-options "--admit_smt_queries true"

#push-options "--z3rlimit 500"

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
  let _:Prims.unit =
    assert (v v_CIPHERTEXT_SIZE ==
        v v_IMPLICIT_REJECTION_HASH_INPUT_SIZE - v Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE)
  in
  let ind_cpa_secret_key, ind_cpa_public_key, ind_cpa_public_key_hash, implicit_rejection_value:(t_Slice
    u8 &
    t_Slice u8 &
    t_Slice u8 &
    t_Slice u8) =
    Libcrux_ml_kem.Types.unpack_private_key v_CPA_SECRET_KEY_SIZE
      v_PUBLIC_KEY_SIZE
      (private_key.Libcrux_ml_kem.Types.f_value <: t_Slice u8)
  in
  let _:Prims.unit =
    assert (ind_cpa_secret_key == slice private_key.f_value (sz 0) v_CPA_SECRET_KEY_SIZE);
    assert (ind_cpa_public_key ==
        slice private_key.f_value v_CPA_SECRET_KEY_SIZE (v_CPA_SECRET_KEY_SIZE +! v_PUBLIC_KEY_SIZE)
      );
    assert (ind_cpa_public_key_hash ==
        slice private_key.f_value
          (v_CPA_SECRET_KEY_SIZE +! v_PUBLIC_KEY_SIZE)
          (v_CPA_SECRET_KEY_SIZE +! v_PUBLIC_KEY_SIZE +! Spec.MLKEM.v_H_DIGEST_SIZE));
    assert (implicit_rejection_value ==
        slice private_key.f_value
          (v_CPA_SECRET_KEY_SIZE +! v_PUBLIC_KEY_SIZE +! Spec.MLKEM.v_H_DIGEST_SIZE)
          (length private_key.f_value))
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
  let _:Prims.unit = eq_intro (Seq.slice to_hash 0 32) decrypted in
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
  let _:Prims.unit =
    lemma_slice_append to_hash decrypted ind_cpa_public_key_hash;
    assert (decrypted == Spec.MLKEM.ind_cpa_decrypt v_K ind_cpa_secret_key ciphertext.f_value);
    assert (to_hash == concat decrypted ind_cpa_public_key_hash)
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
  let _:Prims.unit =
    assert ((shared_secret, pseudorandomness) ==
        split hashed Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE);
    assert (length implicit_rejection_value =
        v_SECRET_KEY_SIZE -! v_CPA_SECRET_KEY_SIZE -! v_PUBLIC_KEY_SIZE -!
        Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE);
    assert (length implicit_rejection_value = Spec.MLKEM.v_SHARED_SECRET_SIZE);
    assert (Spec.MLKEM.v_SHARED_SECRET_SIZE <=. Spec.MLKEM.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE v_K)
  in
  let (to_hash: t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE):t_Array u8
    v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Libcrux_ml_kem.Utils.into_padded_array v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
      implicit_rejection_value
  in
  let _:Prims.unit = eq_intro (Seq.slice to_hash 0 32) implicit_rejection_value in
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
  let _:Prims.unit =
    assert_norm (pow2 32 == 0x100000000);
    assert (v (sz 32) < pow2 32);
    assert (i4.f_PRF_pre (sz 32) to_hash);
    lemma_slice_append to_hash implicit_rejection_value ciphertext.f_value
  in
  let (implicit_rejection_shared_secret: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Libcrux_ml_kem.Hash_functions.f_PRF #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      (sz 32)
      (to_hash <: t_Slice u8)
  in
  let _:Prims.unit =
    assert (implicit_rejection_shared_secret == Spec.Utils.v_PRF (sz 32) to_hash);
    assert (Seq.length ind_cpa_public_key == v v_PUBLIC_KEY_SIZE)
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

#pop-options

#pop-options
