module Libcrux_ml_kem.Ind_cca
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Types in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// Seed size for encapsulation
let v_ENCAPS_SEED_SIZE: usize = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE

/// Seed size for key generation
let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +!
  Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE

/// Serialize the secret key.
val serialize_kem_secret_key
      (v_K v_SERIALIZED_KEY_LEN: usize)
      (#v_Hasher: Type0)
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : Prims.Pure (t_Array u8 v_SERIALIZED_KEY_LEN)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_SERIALIZED_KEY_LEN == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K /\
        Core.Slice.impl__len #u8 private_key == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        Core.Slice.impl__len #u8 public_key == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        Core.Slice.impl__len #u8 implicit_rejection_value == Spec.MLKEM.v_SHARED_SECRET_SIZE)
      (ensures
        fun result ->
          let result:t_Array u8 v_SERIALIZED_KEY_LEN = result in
          result ==
          Seq.append private_key
            (Seq.append public_key (Seq.append (Spec.Utils.v_H public_key) implicit_rejection_value)
            ))

/// Implements [`Variant`], to perform the ML-KEM-specific actions
/// during encapsulation and decapsulation.
/// Specifically,
/// * during encapsulation, the initial randomness is used without prior hashing,
/// * the derivation of the shared secret does not include a hash of the ML-KEM ciphertext.
type t_MlKem = | MlKem : t_MlKem

val validate_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
    : Prims.Pure bool
      (requires
        Spec.MLKEM.is_rank v_K /\
        v_RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CCA_PUBLIC_KEY_SIZE v_K)
      (fun _ -> Prims.l_True)

/// This trait collects differences in specification between ML-KEM
/// (Draft FIPS 203) and the Round 3 CRYSTALS-Kyber submission in the
/// NIST PQ competition.
/// cf. FIPS 203 (Draft), section 1.3
class t_Variant (v_Self: Type0) = {
  f_kdf_pre:
      v_K: usize ->
      v_CIPHERTEXT_SIZE: usize ->
      #v_Hasher: Type0 ->
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      shared_secret: t_Slice u8 ->
      ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE
    -> pred: Type0{(Core.Slice.impl__len #u8 shared_secret <: usize) =. sz 32 ==> pred};
  f_kdf_post:
      v_K: usize ->
      v_CIPHERTEXT_SIZE: usize ->
      #v_Hasher: Type0 ->
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      shared_secret: t_Slice u8 ->
      ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE ->
      res: t_Array u8 (sz 32)
    -> pred: Type0{pred ==> res == shared_secret};
  f_kdf:
      v_K: usize ->
      v_CIPHERTEXT_SIZE: usize ->
      #v_Hasher: Type0 ->
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      x0: t_Slice u8 ->
      x1: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE
    -> Prims.Pure (t_Array u8 (sz 32))
        (f_kdf_pre v_K v_CIPHERTEXT_SIZE #v_Hasher #i1 x0 x1)
        (fun result -> f_kdf_post v_K v_CIPHERTEXT_SIZE #v_Hasher #i1 x0 x1 result);
  f_entropy_preprocess_pre:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      randomness: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 randomness <: usize) =. sz 32 ==> pred};
  f_entropy_preprocess_post:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      t_Slice u8 ->
      t_Array u8 (sz 32)
    -> Type0;
  f_entropy_preprocess:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      x0: t_Slice u8
    -> Prims.Pure (t_Array u8 (sz 32))
        (f_entropy_preprocess_pre v_K #v_Hasher #i3 x0)
        (fun result -> f_entropy_preprocess_post v_K #v_Hasher #i3 x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Variant t_MlKem =
  {
    f_kdf_pre
    =
    (fun
        (v_K: usize)
        (v_CIPHERTEXT_SIZE: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
        (shared_secret: t_Slice u8)
        (_: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
        ->
        (Core.Slice.impl__len #u8 shared_secret <: usize) =. sz 32);
    f_kdf_post
    =
    (fun
        (v_K: usize)
        (v_CIPHERTEXT_SIZE: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
        (shared_secret: t_Slice u8)
        (_: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
        (out: t_Array u8 (sz 32))
        ->
        out == shared_secret);
    f_kdf
    =
    (fun
        (v_K: usize)
        (v_CIPHERTEXT_SIZE: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
        (shared_secret: t_Slice u8)
        (_: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
        ->
        Core.Result.impl__unwrap #(t_Array u8 (sz 32))
          #Core.Array.t_TryFromSliceError
          (Core.Convert.f_try_into #(t_Slice u8)
              #(t_Array u8 (sz 32))
              #FStar.Tactics.Typeclasses.solve
              shared_secret
            <:
            Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError));
    f_entropy_preprocess_pre
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
        (randomness: t_Slice u8)
        ->
        (Core.Slice.impl__len #u8 randomness <: usize) =. sz 32);
    f_entropy_preprocess_post
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
        (randomness: t_Slice u8)
        (out: t_Array u8 (sz 32))
        ->
        true);
    f_entropy_preprocess
    =
    fun
      (v_K: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
        i3:
        Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (randomness: t_Slice u8)
      ->
      Core.Result.impl__unwrap #(t_Array u8 (sz 32))
        #Core.Array.t_TryFromSliceError
        (Core.Convert.f_try_into #(t_Slice u8)
            #(t_Array u8 (sz 32))
            #FStar.Tactics.Typeclasses.solve
            randomness
          <:
          Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError)
  }

/// This code verifies on some machines, runs out of memory on others
val decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i5: t_Variant v_Scheme |}
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32))
      (requires
        Spec.MLKEM.is_rank v_K /\ v_SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K /\
        v_CPA_SECRET_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K /\
        v_T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K /\
        v_C1_SIZE == Spec.MLKEM.v_C1_SIZE v_K /\ v_C2_SIZE == Spec.MLKEM.v_C2_SIZE v_K /\
        v_VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        v_C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE v_K /\ v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA2 == Spec.MLKEM.v_ETA2 v_K /\
        v_ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE v_K /\
        v_IMPLICIT_REJECTION_HASH_INPUT_SIZE == Spec.MLKEM.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE v_K)
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          let expected, valid =
            Spec.MLKEM.ind_cca_decapsulate v_K private_key.f_value ciphertext.f_value
          in
          valid ==> result == expected)

val encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i5: t_Variant v_Scheme |}
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
      (requires
        Spec.MLKEM.is_rank v_K /\ v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        v_T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K /\
        v_C1_SIZE == Spec.MLKEM.v_C1_SIZE v_K /\ v_C2_SIZE == Spec.MLKEM.v_C2_SIZE v_K /\
        v_VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        v_C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE v_K /\ v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA2 == Spec.MLKEM.v_ETA2 v_K /\
        v_ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE v_K)
      (ensures
        fun result ->
          let result:(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
          =
            result
          in
          let expected, valid = Spec.MLKEM.ind_cca_encapsulate v_K public_key.f_value randomness in
          valid ==> (result._1.f_value, result._2) == expected)

/// Packed API
/// Generate a key pair.
/// Depending on the `Vector` and `Hasher` used, this requires different hardware
/// features
val generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (randomness: t_Array u8 (sz 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_CPA_PRIVATE_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        v_PRIVATE_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        v_RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Types.t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
            result
          in
          let expected, valid = Spec.MLKEM.ind_cca_generate_keypair v_K randomness in
          valid ==> (result.f_sk.f_value, result.f_pk.f_value) == expected)
