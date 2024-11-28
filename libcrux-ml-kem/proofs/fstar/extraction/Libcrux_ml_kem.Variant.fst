module Libcrux_ml_kem.Variant
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  ()

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
        true);
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
        (out1: t_Array u8 (sz 32))
        ->
        true);
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
        true);
    f_entropy_preprocess_post
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
        (randomness: t_Slice u8)
        (out1: t_Array u8 (sz 32))
        ->
        true);
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
        true);
    f_cpa_keygen_seed_post
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
        (key_generation_seed: t_Slice u8)
        (out: t_Array u8 (sz 64))
        ->
        true);
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
      Libcrux_ml_kem.Hash_functions.f_G #v_Hasher
        #v_K
        #FStar.Tactics.Typeclasses.solve
        (seed <: t_Slice u8)
  }
