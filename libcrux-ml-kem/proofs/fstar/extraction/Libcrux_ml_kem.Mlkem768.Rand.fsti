module Libcrux_ml_kem.Mlkem768.Rand
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Rand_core in
  ()

/// Generate ML-KEM 768 Key Pair
/// The random number generator `rng` needs to implement `CryptoRng`
/// to sample the required randomness internally.
/// This function returns an [`MlKem768KeyPair`].
val generate_key_pair
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (rng: iimpl_447424039_)
    : Prims.Pure
      (iimpl_447424039_ & Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 2400) (mk_usize 1184))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Encapsulate ML-KEM 768
/// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem768PublicKey`].
/// The random number generator `rng` needs to implement `CryptoRng`
/// to sample the required randomness internally.
val encapsulate
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1184))
      (rng: iimpl_447424039_)
    : Prims.Pure
      (iimpl_447424039_ &
        (Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1088) & t_Array u8 (mk_usize 32)))
      Prims.l_True
      (fun _ -> Prims.l_True)
