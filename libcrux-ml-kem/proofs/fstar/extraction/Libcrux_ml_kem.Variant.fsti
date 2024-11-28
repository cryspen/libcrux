module Libcrux_ml_kem.Variant
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  ()

/// This trait collects differences in specification between ML-KEM
/// (FIPS 203) and the Round 3 CRYSTALS-Kyber submission in the
/// NIST PQ competition.
/// cf. FIPS 203, Appendix C
class t_Variant (v_Self: Type0) = {
  f_kdf_pre:
      v_K: usize ->
      v_CIPHERTEXT_SIZE: usize ->
      #v_Hasher: Type0 ->
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      t_Slice u8 ->
      Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE
    -> Type0;
  f_kdf_post:
      v_K: usize ->
      v_CIPHERTEXT_SIZE: usize ->
      #v_Hasher: Type0 ->
      {| i1: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      t_Slice u8 ->
      Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE ->
      t_Array u8 (sz 32)
    -> Type0;
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
      t_Slice u8
    -> Type0;
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
        (fun result -> f_entropy_preprocess_post v_K #v_Hasher #i3 x0 result);
  f_cpa_keygen_seed_pre:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      t_Slice u8
    -> Type0;
  f_cpa_keygen_seed_post:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      t_Slice u8 ->
      t_Array u8 (sz 64)
    -> Type0;
  f_cpa_keygen_seed:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      x0: t_Slice u8
    -> Prims.Pure (t_Array u8 (sz 64))
        (f_cpa_keygen_seed_pre v_K #v_Hasher #i4 x0)
        (fun result -> f_cpa_keygen_seed_post v_K #v_Hasher #i4 x0 result)
}

/// Implements [`Variant`], to perform the ML-KEM-specific actions
/// during encapsulation and decapsulation.
/// Specifically,
/// * during key generation, the seed hash is domain separated (this is a difference from the FIPS 203 IPD and Kyber)
/// * during encapsulation, the initial randomness is used without prior hashing,
/// * the derivation of the shared secret does not include a hash of the ML-KEM ciphertext.
type t_MlKem = | MlKem : t_MlKem

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:t_Variant t_MlKem
