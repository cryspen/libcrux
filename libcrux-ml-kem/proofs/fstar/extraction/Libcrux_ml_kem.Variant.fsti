module Libcrux_ml_kem.Variant
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  ()

/// Implements [`Variant`], to perform the ML-KEM-specific actions
/// during encapsulation and decapsulation.
/// Specifically,
/// * during key generation, the seed hash is domain separated (this is a difference from the FIPS 203 IPD and Kyber)
/// * during encapsulation, the initial randomness is used without prior hashing,
/// * the derivation of the shared secret does not include a hash of the ML-KEM ciphertext.
type t_MlKem = | MlKem : t_MlKem

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
      randomness: t_Slice u8 ->
      res: t_Array u8 (sz 32)
    -> pred: Type0{pred ==> res == randomness};
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
      seed: t_Slice u8
    -> pred: Type0{(Core.Slice.impl__len #u8 seed <: usize) =. sz 32 ==> pred};
  f_cpa_keygen_seed_post:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      seed: t_Slice u8 ->
      res: t_Array u8 (sz 64)
    -> pred:
      Type0
        { pred ==>
          Seq.length seed == 32 ==>
          res == Spec.Utils.v_G (Seq.append seed (Seq.create 1 (cast v_K <: u8))) };
  f_cpa_keygen_seed:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |} ->
      x0: t_Slice u8
    -> Prims.Pure (t_Array u8 (sz 64))
        (f_cpa_keygen_seed_pre v_K #v_Hasher #i4 x0)
        (fun result -> f_cpa_keygen_seed_post v_K #v_Hasher #i4 x0 result)
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
        (res: t_Array u8 (sz 32))
        ->
        res == shared_secret);
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
        let out:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
        let out:t_Array u8 (sz 32) = Core.Slice.impl__copy_from_slice #u8 out shared_secret in
        out);
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
        (res: t_Array u8 (sz 32))
        ->
        res == randomness);
    f_entropy_preprocess
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
        (randomness: t_Slice u8)
        ->
        let out:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
        let out:t_Array u8 (sz 32) = Core.Slice.impl__copy_from_slice #u8 out randomness in
        out);
    f_cpa_keygen_seed_pre
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
        (key_generation_seed: t_Slice u8)
        ->
        (Core.Slice.impl__len #u8 key_generation_seed <: usize) =. sz 32);
    f_cpa_keygen_seed_post
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
        (key_generation_seed: t_Slice u8)
        (res: t_Array u8 (sz 64))
        ->
        Seq.length key_generation_seed == 32 ==>
        res == Spec.Utils.v_G (Seq.append key_generation_seed (Seq.create 1 (cast v_K <: u8))));
    f_cpa_keygen_seed
    =
    fun
      (v_K: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
        i4:
        Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (key_generation_seed: t_Slice u8)
      ->
      let seed:t_Array u8 (sz 33) = Rust_primitives.Hax.repeat 0uy (sz 33) in
      let seed:t_Array u8 (sz 33) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range seed
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
            }
            <:
            Core.Ops.Range.t_Range usize)
          (Core.Slice.impl__copy_from_slice #u8
              (seed.[ {
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end
                    =
                    Libcrux_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              key_generation_seed
            <:
            t_Slice u8)
      in
      let seed:t_Array u8 (sz 33) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed
          Libcrux_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
          (cast (v_K <: usize) <: u8)
      in
      let _:Prims.unit =
        Lib.Sequence.eq_intro #u8
          #33
          seed
          (Seq.append key_generation_seed (Seq.create 1 (cast v_K <: u8)))
      in
      Libcrux_ml_kem.Hash_functions.f_G #v_Hasher
        #v_K
        #FStar.Tactics.Typeclasses.solve
        (seed <: t_Slice u8)
  }
