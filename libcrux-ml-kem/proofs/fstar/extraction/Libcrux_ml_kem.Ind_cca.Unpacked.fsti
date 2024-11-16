module Libcrux_ml_kem.Ind_cca.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Hash_functions.Portable in
  let open Libcrux_ml_kem.Ind_cpa.Unpacked in
  let open Libcrux_ml_kem.Polynomial in
  let open Libcrux_ml_kem.Types in
  let open Libcrux_ml_kem.Variant in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// An unpacked ML-KEM IND-CCA Private Key
type t_MlKemPrivateKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_ind_cpa_private_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector;
  f_implicit_rejection_value:t_Array u8 (sz 32)
}

/// An unpacked ML-KEM IND-CCA Private Key
type t_MlKemPublicKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_ind_cpa_public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector;
  f_public_key_hash:t_Array u8 (sz 32)
}

/// An unpacked ML-KEM KeyPair
type t_MlKemKeyPairUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_private_key:t_MlKemPrivateKeyUnpacked v_K v_Vector;
  f_public_key:t_MlKemPublicKeyUnpacked v_K v_Vector
}

/// Get the serialized public key.
val impl_4__private_key
      (v_K: usize)
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (t_MlKemPrivateKeyUnpacked v_K v_Vector) Prims.l_True (fun _ -> Prims.l_True)

/// Get the serialized public key.
val impl_4__public_key
      (v_K: usize)
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (t_MlKemPublicKeyUnpacked v_K v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val transpose_a
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (ind_cpa_a:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
    : Prims.Pure
      (t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array
            (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
            result
          in
          forall (i: nat).
            i < v v_K ==>
            (forall (j: nat).
                j < v v_K ==>
                Seq.index (Seq.index result i) j == Seq.index (Seq.index ind_cpa_a j) i))

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core.Default.t_Default (t_MlKemPublicKeyUnpacked v_K v_Vector)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core.Default.t_Default (t_MlKemKeyPairUnpacked v_K v_Vector)

/// Create a new empty unpacked key pair.
val impl_4__new:
    v_K: usize ->
    #v_Vector: Type0 ->
    {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |} ->
    Prims.unit
  -> Prims.Pure (t_MlKemKeyPairUnpacked v_K v_Vector) Prims.l_True (fun _ -> Prims.l_True)

/// Take a serialized private key and generate an unpacked key pair from it.
val keys_from_private_key
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_T_AS_NTT_ENCODED_SIZE:
          usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (key_pair: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (t_MlKemKeyPairUnpacked v_K v_Vector)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K /\
        v_CPA_SECRET_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        v_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K)
      (fun _ -> Prims.l_True)

/// Take a serialized private key and generate an unpacked key pair from it.
val impl_4__from_private_key
      (v_K: usize)
      (#v_Vector: Type0)
      (v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_T_AS_NTT_ENCODED_SIZE:
          usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
    : Prims.Pure (t_MlKemKeyPairUnpacked v_K v_Vector)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K /\
        v_CPA_SECRET_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        v_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K)
      (fun _ -> Prims.l_True)

/// Generate an unpacked key from a serialized key.
val unpack_public_key
      (v_K v_T_AS_NTT_ENCODED_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Hasher #v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (unpacked_public_key: t_MlKemPublicKeyUnpacked v_K v_Vector)
    : Prims.Pure (t_MlKemPublicKeyUnpacked v_K v_Vector)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        v_T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K)
      (ensures
        fun unpacked_public_key_future ->
          let unpacked_public_key_future:t_MlKemPublicKeyUnpacked v_K v_Vector =
            unpacked_public_key_future
          in
          let public_key_hash, (seed, (deserialized_pk, (matrix_A, valid))) =
            Spec.MLKEM.ind_cca_unpack_public_key v_K public_key.f_value
          in
          (valid ==>
            Libcrux_ml_kem.Polynomial.to_spec_matrix_t #v_K
              #v_Vector
              unpacked_public_key_future.f_ind_cpa_public_key.f_A ==
            matrix_A) /\
          Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
            #v_Vector
            unpacked_public_key_future.f_ind_cpa_public_key.f_t_as_ntt ==
          deserialized_pk /\ unpacked_public_key_future.f_ind_cpa_public_key.f_seed_for_A == seed /\
          unpacked_public_key_future.f_public_key_hash == public_key_hash)

val encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (public_key: t_MlKemPublicKeyUnpacked v_K v_Vector)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
      (requires
        Spec.MLKEM.is_rank v_K /\ v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA2 == Spec.MLKEM.v_ETA2 v_K /\
        v_ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE v_K /\
        v_C1_SIZE == Spec.MLKEM.v_C1_SIZE v_K /\ v_C2_SIZE == Spec.MLKEM.v_C2_SIZE v_K /\
        v_VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        v_VECTOR_U_BLOCK_LEN == Spec.MLKEM.v_C1_BLOCK_SIZE v_K /\
        v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K)
      (ensures
        fun temp_0_ ->
          let ciphertext_result, shared_secret_array:(Libcrux_ml_kem.Types.t_MlKemCiphertext
            v_CIPHERTEXT_SIZE &
            t_Array u8 (sz 32)) =
            temp_0_
          in
          let ciphertext, shared_secret =
            Spec.MLKEM.ind_cca_unpack_encapsulate v_K
              public_key.f_public_key_hash
              (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
                  #v_Vector
                  public_key.f_ind_cpa_public_key.f_t_as_ntt)
              (Libcrux_ml_kem.Polynomial.to_spec_matrix_t #v_K
                  #v_Vector
                  public_key.f_ind_cpa_public_key.f_A)
              randomness
          in
          ciphertext_result.f_value == ciphertext /\ shared_secret_array == shared_secret)

/// Get the serialized public key.
val impl_3__serialized_mut
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemPublicKeyUnpacked v_K v_Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (requires
        Spec.MLKEM.is_rank v_K /\
        v_RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        (forall (i: nat).
            i < v v_K ==>
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index self
                    .f_ind_cpa_public_key
                    .f_t_as_ntt
                  i)))
      (ensures
        fun serialized_future ->
          let serialized_future:Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE =
            serialized_future
          in
          serialized_future.f_value ==
          Seq.append (Spec.MLKEM.vector_encode_12 #v_K
                (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
                    #v_Vector
                    self.f_ind_cpa_public_key.f_t_as_ntt))
            self.f_ind_cpa_public_key.f_seed_for_A)

/// Get the serialized public key.
val impl_4__serialized_public_key_mut
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (requires
        Spec.MLKEM.is_rank v_K /\
        v_RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        (forall (i: nat).
            i < v v_K ==>
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index self.f_public_key
                    .f_ind_cpa_public_key
                    .f_t_as_ntt
                  i)))
      (ensures
        fun serialized_future ->
          let serialized_future:Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE =
            serialized_future
          in
          serialized_future.f_value ==
          Seq.append (Spec.MLKEM.vector_encode_12 #v_K
                (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
                    #v_Vector
                    self.f_public_key.f_ind_cpa_public_key.f_t_as_ntt))
            self.f_public_key.f_ind_cpa_public_key.f_seed_for_A)

/// Get the serialized public key.
val impl_3__serialized
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemPublicKeyUnpacked v_K v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (requires
        Spec.MLKEM.is_rank v_K /\
        v_RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        (forall (i: nat).
            i < v v_K ==>
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index self
                    .f_ind_cpa_public_key
                    .f_t_as_ntt
                  i)))
      (ensures
        fun res ->
          let res:Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE = res in
          res.f_value ==
          Seq.append (Spec.MLKEM.vector_encode_12 #v_K
                (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
                    #v_Vector
                    self.f_ind_cpa_public_key.f_t_as_ntt))
            self.f_ind_cpa_public_key.f_seed_for_A)

/// Get the serialized public key.
val impl_4__serialized_public_key
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (requires
        Spec.MLKEM.is_rank v_K /\
        v_RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        (forall (i: nat).
            i < v v_K ==>
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index self.f_public_key
                    .f_ind_cpa_public_key
                    .f_t_as_ntt
                  i)))
      (ensures
        fun res ->
          let res:Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE = res in
          res.f_value ==
          Seq.append (Spec.MLKEM.vector_encode_12 #v_K
                (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
                    #v_Vector
                    self.f_public_key.f_ind_cpa_public_key.f_t_as_ntt))
            self.f_public_key.f_ind_cpa_public_key.f_seed_for_A)

/// Generate Unpacked Keys
val generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme |}
      (randomness: t_Array u8 (sz 64))
      (out: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (t_MlKemKeyPairUnpacked v_K v_Vector)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K)
      (ensures
        fun out_future ->
          let out_future:t_MlKemKeyPairUnpacked v_K v_Vector = out_future in
          let ((m_A, public_key_hash), implicit_rejection_value), valid =
            Spec.MLKEM.ind_cca_unpack_generate_keypair v_K randomness
          in
          valid ==>
          Libcrux_ml_kem.Polynomial.to_spec_matrix_t #v_K
            #v_Vector
            out_future.f_public_key.f_ind_cpa_public_key.f_A ==
          m_A /\ out_future.f_public_key.f_public_key_hash == public_key_hash /\
          out_future.f_private_key.f_implicit_rejection_value == implicit_rejection_value)

/// Get the serialized private key.
val impl_4__serialized_private_key_mut
      (v_K: usize)
      (#v_Vector: Type0)
      (v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT:
          usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the serialized private key.
val impl_4__serialized_private_key
      (v_K: usize)
      (#v_Vector: Type0)
      (v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT:
          usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

val decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (key_pair: t_MlKemKeyPairUnpacked v_K v_Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32))
      (requires
        Spec.MLKEM.is_rank v_K /\ v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA2 == Spec.MLKEM.v_ETA2 v_K /\
        v_ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE v_K /\
        v_C1_SIZE == Spec.MLKEM.v_C1_SIZE v_K /\ v_C2_SIZE == Spec.MLKEM.v_C2_SIZE v_K /\
        v_VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        v_C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE v_K /\
        v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K /\
        v_IMPLICIT_REJECTION_HASH_INPUT_SIZE == Spec.MLKEM.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE v_K)
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          result ==
          Spec.MLKEM.ind_cca_unpack_decapsulate v_K
            key_pair.f_public_key.f_public_key_hash
            key_pair.f_private_key.f_implicit_rejection_value
            ciphertext.f_value
            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
                #v_Vector
                key_pair.f_private_key.f_ind_cpa_private_key.f_secret_as_ntt)
            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
                #v_Vector
                key_pair.f_public_key.f_ind_cpa_public_key.f_t_as_ntt)
            (Libcrux_ml_kem.Polynomial.to_spec_matrix_t #v_K
                #v_Vector
                key_pair.f_public_key.f_ind_cpa_public_key.f_A))
