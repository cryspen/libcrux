module Libcrux_ml_kem.Mlkem1024.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cca.Incremental.Types in
  ()

/// Get the size of the first public key in bytes.
val pk1_len: Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// Get the size of the second public key in bytes.
val pk2_len: Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The size of the key pair in bytes.
val key_pair_len: Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The size of the encaps state in bytes.
val encaps_state_len: Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// Generate a key pair and write it into `key_pair`.
/// `key_pair.len()` must be of size `key_pair_len()`.
val generate_key_pair (randomness: t_Array u8 (mk_usize 64)) (key_pair: t_Slice u8)
    : Prims.Pure
      (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
      ) Prims.l_True (fun _ -> Prims.l_True)

/// Validate that the two parts `pk1` and `pk2` are consistent.
val validate_pk (pk1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1) (pk2: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Encapsulate the first part of the ciphertext.
/// Returns an [`Error`] if the provided input or output don't have
/// the appropriate sizes.
val encapsulate1
      (pk1: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
      (state shared_secret: t_Slice u8)
    : Prims.Pure
      (t_Slice u8 & t_Slice u8 &
        Core.Result.t_Result
          (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 1408))
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) Prims.l_True (fun _ -> Prims.l_True)

/// Encapsulate the second part of the ciphertext.
/// The second part of the public key is passed in as byte slice.
/// [`Error::InvalidInputLength`] is returned if `public_key_part` is too
/// short.
val encapsulate2 (state public_key_part: t_Slice u8)
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 (mk_usize 160))
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) Prims.l_True (fun _ -> Prims.l_True)

/// Decapsulate incremental ciphertexts.
val decapsulate_incremental_key
      (private_key: t_Slice u8)
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 1408))
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 (mk_usize 160))
    : Prims.Pure
      (Core.Result.t_Result (t_Array u8 (mk_usize 32))
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) Prims.l_True (fun _ -> Prims.l_True)
