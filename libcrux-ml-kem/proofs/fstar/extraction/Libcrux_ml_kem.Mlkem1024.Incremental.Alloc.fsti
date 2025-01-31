module Libcrux_ml_kem.Mlkem1024.Incremental.Alloc
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

/// Generate a new key pair for incremental encapsulation.
val generate_key_pair (randomness: t_Array u8 (mk_usize 64))
    : Prims.Pure
      (Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
          Alloc.Alloc.t_Global) Prims.l_True (fun _ -> Prims.l_True)

/// Encapsulate the first part of the ciphertext.
val encapsulate1
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 1408) &
        Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
          Alloc.Alloc.t_Global &
        t_Array u8 (mk_usize 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Encapsulate the second part of the ciphertext.
/// The second part of the public key is passed in as byte slice.
/// [`Error::InvalidInputLength`] is returned if `public_key_part` is too
/// short.
val encapsulate2
      (state: dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
      (public_key_part: t_Slice u8)
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 (mk_usize 160))
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) Prims.l_True (fun _ -> Prims.l_True)

/// Decapsulate incremental ciphertexts.
val decapsulate
      (private_key: dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 1408))
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 (mk_usize 160))
    : Prims.Pure (t_Array u8 (mk_usize 32)) Prims.l_True (fun _ -> Prims.l_True)
